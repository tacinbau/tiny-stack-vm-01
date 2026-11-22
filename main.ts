import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const IN = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const enc = new TextEncoder();

// Opcode table: [byte, immediate bytes, pops, pushes] for every opcode of the ISA.
const OPS = [[0,0,0,0],[1,1,0,1],[2,4,0,1],[3,0,1,0],[4,0,1,2],[5,0,2,2],[6,0,2,3],[7,0,3,3],[16,0,2,1],[17,0,2,1],[18,0,2,1],[19,0,2,1],[20,0,2,1],[21,0,2,1],[22,0,2,1],[23,0,1,1],[24,0,2,1],[25,0,2,1],[26,0,2,1],[27,0,1,1],[28,0,2,1],[29,0,2,1],[30,0,2,1],[32,0,2,1],[33,0,2,1],[34,0,2,1],[48,2,0,0],[49,2,1,0],[50,2,1,0],[51,2,0,0],[52,0,0,0],[64,0,1,1],[65,0,2,0],[80,0,1,0],[81,0,1,0],[82,0,0,1],[83,0,1,0]];
const IMM = new Uint8Array(256);
const POP = new Uint8Array(256);
const PSH = new Uint8Array(256);
const KNOWN = new Uint8Array(256);
for (const [b, i, p, q] of OPS) { IMM[b] = i; POP[b] = p; PSH[b] = q; KNOWN[b] = 1; }

// Runs one program on its input bytes. Returns [output buffer, output length, exit code].
// Traps return their trap code as the exit code and keep the output written so far.
function run(prog, input) {
  const n = prog.length;
  const D = new Int32Array(256); // data stack
  const C = new Int32Array(64); // call stack
  const M = new Int32Array(256); // memory words
  const out = new Uint8Array(65536);
  let sp = 0, cp = 0, ol = 0, ip = 0, pc = 0, steps = 0;
  for (;;) {
    if (steps === 1000000) return [out, ol, 10];
    if (pc < 0 || pc >= n) return [out, ol, 9];
    const op = prog[pc];
    if (!KNOWN[op]) return [out, ol, 5];
    const imm = IMM[op];
    if (pc + imm >= n) return [out, ol, 9];
    steps++;
    const nx = pc + 1 + imm;
    const pops = POP[op], pushes = PSH[op];
    if (sp < pops) return [out, ol, 2];
    if (sp - pops + pushes > 256) return [out, ol, 3];
    pc = nx;
    switch (op) {
      case 0: return [out, ol, 0]; // HALT
      case 1: D[sp++] = (prog[nx - 1] << 24) >> 24; break; // PUSH8, sign-extended
      case 2: D[sp++] = prog[nx - 4] | (prog[nx - 3] << 8) | (prog[nx - 2] << 16) | (prog[nx - 1] << 24); break; // PUSH32
      case 3: sp--; break; // POP
      case 4: D[sp] = D[sp - 1]; sp++; break; // DUP
      case 5: { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; break; } // SWAP
      case 6: D[sp] = D[sp - 2]; sp++; break; // OVER
      case 7: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; } // ROT
      case 23: D[sp - 1] = -D[sp - 1] | 0; break; // NEG
      case 27: D[sp - 1] = ~D[sp - 1]; break; // NOT
      case 16: case 17: case 18: case 19: case 20: case 21: case 22:
      case 24: case 25: case 26: case 28: case 29: case 30: case 32: case 33: case 34: {
        const b = D[sp - 1];
        const a = D[sp - 2];
        let r;
        if (op === 16) r = (a + b) | 0; // ADD
        else if (op === 17) r = (a - b) | 0; // SUB
        else if (op === 18) r = Math.imul(a, b); // MUL, low 32 bits
        else if (op === 19) { if (b === 0) return [out, ol, 4]; r = a === -2147483648 && b === -1 ? a : (a / b) | 0; } // DIV
        else if (op === 20) { if (b === 0) return [out, ol, 4]; r = b === -1 ? 0 : (a % b) | 0; } // MOD
        else if (op === 21) { if (b === 0) return [out, ol, 4]; r = Math.floor((a >>> 0) / (b >>> 0)) | 0; } // DIVU
        else if (op === 22) { if (b === 0) return [out, ol, 4]; r = ((a >>> 0) % (b >>> 0)) | 0; } // MODU
        else if (op === 24) r = a & b; // AND
        else if (op === 25) r = a | b; // OR
        else if (op === 26) r = a ^ b; // XOR
        else if (op === 28) r = a << (b & 31); // SHL
        else if (op === 29) r = a >> (b & 31); // SHR, arithmetic
        else if (op === 30) r = (a >>> (b & 31)) | 0; // SHRU, logical
        else if (op === 32) r = a === b ? 1 : 0; // EQ
        else if (op === 33) r = a < b ? 1 : 0; // LT, signed
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU, unsigned
        sp -= 2;
        D[sp++] = r;
        break;
      }
      case 48: case 49: case 50: { // JMP, JZ, JNZ: signed 16-bit offset from next instruction
        const rel = ((prog[nx - 2] | (prog[nx - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 48) { const v = D[--sp]; take = op === 49 ? v === 0 : v !== 0; }
        if (take) pc = nx + rel;
        break;
      }
      case 51: { // CALL: unsigned 16-bit absolute target
        if (cp === 64) return [out, ol, 7];
        C[cp++] = nx;
        pc = prog[nx - 2] | (prog[nx - 1] << 8);
        break;
      }
      case 52: { // RET
        if (cp === 0) return [out, ol, 8];
        pc = C[--cp];
        break;
      }
      case 64: { // LOAD
        const addr = D[sp - 1];
        if (addr < 0 || addr >= 256) return [out, ol, 6];
        D[sp - 1] = M[addr];
        break;
      }
      case 65: { // STORE: ( v addr -- )
        const addr = D[sp - 1];
        const v = D[sp - 2];
        if (addr < 0 || addr >= 256) return [out, ol, 6];
        sp -= 2;
        M[addr] = v;
        break;
      }
      case 80: { // PRINT: decimal ASCII, no newline
        const bytes = enc.encode(String(D[sp - 1]));
        if (ol + bytes.length > 65536) return [out, ol, 11];
        sp--;
        out.set(bytes, ol);
        ol += bytes.length;
        break;
      }
      case 81: { // PUTC: low byte
        if (ol + 1 > 65536) return [out, ol, 11];
        out[ol++] = D[--sp] & 255;
        break;
      }
      case 82: D[sp++] = ip < input.length ? input[ip++] : -1; break; // IN, -1 at EOF
      case 83: return [out, ol, D[--sp] & 255]; // EXIT, low byte
    }
  }
}

for (const id of readdirSync(IN).sort()) {
  const prog = readFileSync(join(IN, id, 'program.bin'));
  let input;
  try { input = readFileSync(join(IN, id, 'input.bin')); } catch { input = Buffer.alloc(0); }
  const [out, ol, exit] = run(prog, input);
  mkdirSync(join(OUT, id), { recursive: true });
  writeFileSync(join(OUT, id, 'stdout.bin'), out.subarray(0, ol));
  writeFileSync(join(OUT, id, 'exit.txt'), exit + '\n');
}
