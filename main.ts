// tiny-stack-vm: an interpreter for make.fun's tiny stack ISA, written from
// the kit's spec (generator/subject/ISA.md); see the README for what it does.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";

const IN = process.env.MAKEFUN_INPUT_DIR ?? "/input";
const OUT = process.env.MAKEFUN_OUTPUT_DIR ?? "/output";

function read(p) {
  try {
    return readFileSync(p);
  } catch {
    return new Uint8Array(0);
  }
}

// Runs one program to its end; returns [output bytes, exit code].
function run(P, I) {
  const S = new Int32Array(256); // data stack
  const C = new Int32Array(64); // call stack
  const M = new Int32Array(256); // memory
  const O = new Uint8Array(65536); // output
  const n = P.length;
  let sp = 0, cp = 0, ol = 0, pc = 0, ip = 0, steps = 0;
  const done = (code) => [O.subarray(0, ol), code];
  for (;;) {
    if (steps >= 1000000) return done(10); // step limit
    if (pc < 0 || pc >= n) return done(9); // pc outside the program
    const op = P[pc];
    steps += 1;
    if (op >= 0x10 && op <= 0x22 && op !== 0x17 && op !== 0x1b && op !== 0x1f) {
      // binary ops: ( a b -- r ), b on top
      if (sp < 2) return done(2);
      const b = S[--sp], a = S[sp - 1];
      let r;
      switch (op) {
        case 0x10: r = (a + b) | 0; break; // ADD
        case 0x11: r = (a - b) | 0; break; // SUB
        case 0x12: r = Math.imul(a, b); break; // MUL
        case 0x13: if (b === 0) return done(4); r = Math.trunc(a / b) | 0; break; // DIV
        case 0x14: if (b === 0) return done(4); r = (a % b) | 0; break; // MOD
        case 0x15: if (b === 0) return done(4); r = Math.trunc((a >>> 0) / (b >>> 0)) | 0; break; // DIVU
        case 0x16: if (b === 0) return done(4); r = ((a >>> 0) % (b >>> 0)) | 0; break; // MODU
        case 0x18: r = a & b; break; // AND
        case 0x19: r = a | b; break; // OR
        case 0x1a: r = a ^ b; break; // XOR
        case 0x1c: r = a << (b & 31); break; // SHL
        case 0x1d: r = a >> (b & 31); break; // SHR
        case 0x1e: r = (a >>> (b & 31)) | 0; break; // SHRU
        case 0x20: r = a === b ? 1 : 0; break; // EQ
        case 0x21: r = a < b ? 1 : 0; break; // LT
        default: r = (a >>> 0) < (b >>> 0) ? 1 : 0; break; // LTU (0x22)
      }
      S[sp - 1] = r;
      pc += 1;
      continue;
    }
    if (op >= 0x30 && op <= 0x33) {
      // JMP, JZ, JNZ, CALL: a 2-byte immediate follows
      if (pc + 3 > n) return done(9);
      const imm = P[pc + 1] | (P[pc + 2] << 8);
      if (op === 0x33) { // CALL: unsigned address
        if (cp >= 64) return done(7);
        C[cp++] = pc + 3;
        pc = imm;
      } else { // signed offset from the next instruction
        const off = (imm << 16) >> 16;
        if (op === 0x30) pc = pc + 3 + off; // JMP
        else {
          if (sp < 1) return done(2);
          const v = S[--sp];
          pc = (op === 0x31 ? v === 0 : v !== 0) ? pc + 3 + off : pc + 3; // JZ / JNZ
        }
      }
      continue;
    }
    switch (op) {
      case 0x00: return done(0); // HALT
      case 0x01: { // PUSH8
        if (pc + 2 > n) return done(9);
        if (sp >= 256) return done(3);
        const b = P[pc + 1];
        S[sp++] = b >= 128 ? b - 256 : b;
        pc += 2;
        break;
      }
      case 0x02: // PUSH32
        if (pc + 5 > n) return done(9);
        if (sp >= 256) return done(3);
        S[sp++] = P[pc + 1] | (P[pc + 2] << 8) | (P[pc + 3] << 16) | (P[pc + 4] << 24);
        pc += 5;
        break;
      case 0x03: if (sp < 1) return done(2); sp -= 1; pc += 1; break; // POP
      case 0x04: // DUP
        if (sp < 1) return done(2);
        if (sp >= 256) return done(3);
        S[sp] = S[sp - 1]; sp += 1; pc += 1; break;
      case 0x05: { // SWAP
        if (sp < 2) return done(2);
        const t = S[sp - 1];
        S[sp - 1] = S[sp - 2]; S[sp - 2] = t; pc += 1; break;
      }
      case 0x06: // OVER
        if (sp < 2) return done(2);
        if (sp >= 256) return done(3);
        S[sp] = S[sp - 2]; sp += 1; pc += 1; break;
      case 0x07: { // ROT: ( a b c -- b c a )
        if (sp < 3) return done(2);
        const a = S[sp - 3];
        S[sp - 3] = S[sp - 2]; S[sp - 2] = S[sp - 1]; S[sp - 1] = a; pc += 1; break;
      }
      case 0x17: if (sp < 1) return done(2); S[sp - 1] = (-S[sp - 1]) | 0; pc += 1; break; // NEG
      case 0x1b: if (sp < 1) return done(2); S[sp - 1] = ~S[sp - 1]; pc += 1; break; // NOT
      case 0x34: if (cp < 1) return done(8); pc = C[--cp]; break; // RET
      case 0x40: { // LOAD
        if (sp < 1) return done(2);
        const a = S[sp - 1];
        if (a < 0 || a > 255) return done(6);
        S[sp - 1] = M[a]; pc += 1; break;
      }
      case 0x41: { // STORE: ( v addr -- )
        if (sp < 2) return done(2);
        const a = S[sp - 1];
        if (a < 0 || a > 255) return done(6);
        M[a] = S[sp - 2]; sp -= 2; pc += 1; break;
      }
      case 0x50: { // PRINT, decimal ASCII
        if (sp < 1) return done(2);
        const s = String(S[--sp]);
        if (ol + s.length > 65536) return done(11); // writes nothing
        for (let i = 0; i < s.length; i++) O[ol++] = s.charCodeAt(i);
        pc += 1; break;
      }
      case 0x51: // PUTC
        if (sp < 1) return done(2);
        if (ol >= 65536) return done(11);
        O[ol++] = S[--sp] & 255; pc += 1; break;
      case 0x52: // IN
        if (sp >= 256) return done(3);
        S[sp++] = ip < I.length ? I[ip++] : -1; pc += 1; break;
      case 0x53: if (sp < 1) return done(2); return done(S[sp - 1] & 255); // EXIT
      default: return done(5); // unknown opcode
    }
  }
}

for (const id of readdirSync(IN).sort()) {
  const [bytes, code] = run(read(join(IN, id, "program.bin")), read(join(IN, id, "input.bin")));
  mkdirSync(join(OUT, id), { recursive: true });
  writeFileSync(join(OUT, id, "stdout.bin"), bytes);
  writeFileSync(join(OUT, id, "exit.txt"), String(code));
}
