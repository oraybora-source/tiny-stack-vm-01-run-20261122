// Tiny stack VM, ISA v1 — a faithful interpreter, written from ISA.md.
// One run answers every instance: /input/<id>/{program,input}.bin
// -> /output/<id>/{stdout.bin,exit.txt}. Pure: no clock, no network.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
const E = new TextEncoder();
function run(p, q) {
  const n = p.length, D = new Int32Array(256), C = new Int32Array(64),
    M = new Int32Array(256), O = new Uint8Array(65536);
  let s = 0, c = 0, l = 0, i = 0, x = 0, t = 0;
  const e = (v) => ({ o: O.slice(0, l), e: v });
  for (;;) {
    if (t === 1e6) return e(10); // step limit, checked first
    if (x < 0 || x >= n) return e(9); // pc outside the program
    const o = p[x];
    if (!(o < 8 || (o >= 16 && o <= 30) || (o >= 32 && o <= 34) || (o >= 48 && o <= 52)
      || (o >= 64 && o <= 65) || (o >= 80 && o <= 83))) return e(5); // unknown opcode
    const m = o === 1 ? 1 : o === 2 ? 4 : o >= 48 && o <= 51 ? 2 : 0;
    if (x + m >= n) return e(9); // immediate cut off by the end
    t++;
    const y = x + 1 + m;
    let a = 0, b = 0; // pops, pushes
    if (o === 7) a = 3;
    else if (o === 3 || o === 4 || o === 23 || o === 27 || o === 49 || o === 50
      || o === 64 || o === 80 || o === 81 || o === 83) a = 1;
    else if (o === 5 || o === 6 || o === 65 || (o >= 16 && o <= 34 && o !== 23 && o !== 27)) a = 2;
    if (o === 1 || o === 2 || o === 23 || o === 27 || o === 64 || o === 82
      || (o >= 16 && o <= 34 && o !== 23 && o !== 27)) b = 1;
    else if (o === 4 || o === 5) b = 2;
    else if (o === 6 || o === 7) b = 3;
    if (s < a) return e(2);
    if (s - a + b > 256) return e(3);
    x = y;
    if (o >= 16 && o <= 34 && o !== 23 && o !== 27) { // binary op
      const d = D[s - 1], g = D[s - 2];
      let r;
      if (o === 16) r = (g + d) | 0;
      else if (o === 17) r = (g - d) | 0;
      else if (o === 18) r = Math.imul(g, d);
      else if (o === 19) { if (!d) return e(4); r = (g / d) | 0; } // INT_MIN/-1 wraps via |0
      else if (o === 20) { if (!d) return e(4); r = (g % d) | 0; } // sign of g; x%-1 -> 0
      else if (o === 21) { if (!d) return e(4); r = Math.floor((g >>> 0) / (d >>> 0)) | 0; }
      else if (o === 22) { if (!d) return e(4); r = ((g >>> 0) % (d >>> 0)) | 0; }
      else if (o === 24) r = g & d;
      else if (o === 25) r = g | d;
      else if (o === 26) r = g ^ d;
      else if (o === 28) r = g << (d & 31);
      else if (o === 29) r = g >> (d & 31);
      else if (o === 30) r = (g >>> (d & 31)) | 0;
      else if (o === 32) r = g === d ? 1 : 0;
      else if (o === 33) r = g < d ? 1 : 0;
      else r = (g >>> 0) < (d >>> 0) ? 1 : 0;
      s -= 2;
      D[s++] = r;
      continue;
    }
    switch (o) {
      case 0: return e(0);
      case 1: D[s++] = (p[y - 1] << 24) >> 24; break;
      case 2: D[s++] = p[y - 4] | (p[y - 3] << 8) | (p[y - 2] << 16) | (p[y - 1] << 24); break;
      case 3: s--; break;
      case 4: D[s] = D[s - 1]; s++; break;
      case 5: { const z = D[s - 1]; D[s - 1] = D[s - 2]; D[s - 2] = z; break; }
      case 6: D[s] = D[s - 2]; s++; break;
      case 7: { const z = D[s - 3]; D[s - 3] = D[s - 2]; D[s - 2] = D[s - 1]; D[s - 1] = z; break; }
      case 23: D[s - 1] = (-D[s - 1]) | 0; break;
      case 27: D[s - 1] = ~D[s - 1]; break;
      case 48: case 49: case 50: {
        const r = ((p[y - 2] | (p[y - 1] << 8)) << 16) >> 16;
        let k = true;
        if (o !== 48) { const v = D[--s]; k = o === 49 ? v === 0 : v !== 0; }
        if (k) x = y + r;
        break;
      }
      case 51:
        if (c === 64) return e(7);
        C[c++] = y;
        x = p[y - 2] | (p[y - 1] << 8);
        break;
      case 52:
        if (!c) return e(8);
        x = C[--c];
        break;
      case 64: {
        const a2 = D[s - 1];
        if (a2 < 0 || a2 >= 256) return e(6);
        D[s - 1] = M[a2];
        break;
      }
      case 65: {
        const a2 = D[s - 1], v = D[s - 2];
        if (a2 < 0 || a2 >= 256) return e(6);
        s -= 2;
        M[a2] = v;
        break;
      }
      case 80: {
        const z = E.encode(String(D[s - 1]));
        if (l + z.length > 65536) return e(11);
        s--;
        O.set(z, l);
        l += z.length;
        break;
      }
      case 81:
        if (l + 1 > 65536) return e(11);
        O[l++] = D[--s] & 255;
        break;
      case 82: D[s++] = i < q.length ? q[i++] : -1; break;
      case 83: return e(D[--s] & 255);
    }
  }
}
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(new Uint8Array(readFileSync(join(I, id, 'program.bin'))),
    new Uint8Array(readFileSync(join(I, id, 'input.bin'))));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.o);
  writeFileSync(join(O, id, 'exit.txt'), r.e + '\n');
}
