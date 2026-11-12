///|
/// 面格 𝔽：由 (i=0)、(i=1) 生成、滿足 (i=0)∧(i=1) = 0 的有界分配格。
/// 一個「面」是部分賦值：`zeros`、`ones` 為互斥的名字位元集，編碼為 zeros | ones << MAX_NAMES。
/// 面格元素的正規形為面的反鏈（越少約束的面越大）。
pub(all) struct Face {
  fs : Array[Int32]
}

///|
fn face_consistent(f : Int32) -> Bool {
  let zeros = f & ((1 << MAX_NAMES) - 1)
  let ones = f >> MAX_NAMES
  (zeros & ones) == 0
}

///|
fn face_minimize(raw : Array[Int32]) -> Array[Int32] {
  let ok : Array[Int32] = []
  for f in raw {
    if face_consistent(f) {
      ok.push(f)
    }
  }
  minimize(ok)
}

///|
pub fn Face::bot() -> Face {
  { fs: [], }
}

///|
pub fn Face::top() -> Face {
  { fs: [0], }
}

///|
/// 原子面 (i = 0) 或 (i = 1)。
pub fn Face::eq(i : Int32, one~ : Bool) -> Face {
  if one {
    { fs: [1 << (i + MAX_NAMES)], }
  } else {
    { fs: [1 << i], }
  }
}

///|
pub fn Face::join(self : Face, other : Face) -> Face {
  let raw = self.fs.copy()
  for f in other.fs {
    raw.push(f)
  }
  { fs: face_minimize(raw), }
}

///|
pub fn Face::meet(self : Face, other : Face) -> Face {
  let raw : Array[Int32] = []
  for a in self.fs {
    for b in other.fs {
      raw.push(a | b)
    }
  }
  { fs: face_minimize(raw), }
}

///|
pub fn Face::same(self : Face, other : Face) -> Bool {
  self.fs == other.fs
}

///|
pub fn Face::leq(self : Face, other : Face) -> Bool {
  for f in self.fs {
    let mut covered = false
    for g in other.fs {
      if (g & f) == g {
        covered = true
        break
      }
    }
    if !covered {
      return false
    }
  }
  true
}

///|
/// 格同態 (r = 1) : 𝕀 → 𝔽。單項式的文字 i ↦ (i=1)、¬i ↦ (i=0)；同含 i 與 ¬i 者為 ⊥。
pub fn Dm::eq_one(self : Dm) -> Face {
  let raw : Array[Int32] = []
  for m in self.ms {
    let pos = m & ((1 << MAX_NAMES) - 1)
    let neg = m >> MAX_NAMES
    raw.push(neg | (pos << MAX_NAMES))
  }
  { fs: face_minimize(raw), }
}

///|
/// (r = 0) 定義為 (¬r = 1)。
pub fn Dm::eq_zero(self : Dm) -> Face {
  self.neg().eq_one()
}

///|
/// n 維立方體的 3ⁿ 個面以三進位編碼：第 i 位 0 = 自由、1 = (i=0)、2 = (i=1)。
/// 面格元素的語義：被它蓋住的面的集合——面偏序上的篩（下閉集）。
/// 回傳長度 3ⁿ 的布林陣列。
pub fn Face::sieve(self : Face, n : Int32) -> Array[Bool] {
  let mut total = 1
  for _ in 0..<n {
    total *= 3
  }
  let out = Array::make(total, false)
  for code in 0..<total {
    let mut zeros = 0
    let mut ones = 0
    let mut c = code
    for i in 0..<n {
      let d = c % 3
      c = c / 3
      if d == 1 {
        zeros = zeros | (1 << i)
      } else if d == 2 {
        ones = ones | (1 << i)
      }
    }
    let cube = zeros | (ones << MAX_NAMES)
    for g in self.fs {
      if (g & cube) == g {
        out[code] = true
        break
      }
    }
  }
  out
}

///|
/// 面格於 n 個名字上的全部元素（閉包列舉）。
pub fn face_lattice(n : Int32, limit~ : Int32) -> Array[Face] {
  let seen : Map[String, Bool] = Map([])
  let elems : Array[Face] = []
  let add = fn(x : Face) {
    let sb = StringBuilder()
    for f in x.fs {
      sb.write_string("\{f},")
    }
    let k = sb.to_string()
    if !seen.contains(k) {
      seen[k] = true
      elems.push(x)
    }
  }
  add(Face::bot())
  add(Face::top())
  for i in 0..<n {
    add(Face::eq(i, one=false))
    add(Face::eq(i, one=true))
  }
  let mut frontier = 0
  while frontier < elems.length() && elems.length() < limit {
    let x = elems[frontier]
    frontier += 1
    let upto = elems.length()
    for j in 0..<upto {
      add(x.meet(elems[j]))
      add(x.join(elems[j]))
    }
  }
  elems
}

///|
/// 面偏序上的篩的個數（直接以下閉性枚舉 2^(3ⁿ) 個子集；n ≤ 2）。
/// 不含空面：全體面皆非空，故篩 ↔ 反鏈。
pub fn count_sieves(n : Int32) -> Int32 {
  let mut total = 1
  for _ in 0..<n {
    total *= 3
  }
  // refines[a] = 比 a 約束更多（更小）的面集合
  let below : Array[Int32] = Array::make(total, 0)
  for a in 0..<total {
    for b in 0..<total {
      // b ≤ a ⇔ a 的每個固定座標在 b 中取同值
      let mut ok = true
      let mut ca = a
      let mut cb = b
      for _ in 0..<n {
        let da = ca % 3
        let db = cb % 3
        ca = ca / 3
        cb = cb / 3
        if da != 0 && da != db {
          ok = false
        }
      }
      if ok {
        below[a] = below[a] | (1 << b)
      }
    }
  }
  let mut count = 0
  for s in 0..<(1 << total) {
    let mut closed = true
    for a in 0..<total {
      if ((s >> a) & 1) == 1 && (below[a] & s) != below[a] {
        closed = false
        break
      }
    }
    if closed {
      count += 1
    }
  }
  count
}

///|
/// 面格 ≅ 篩格（Grothendieck 拓撲語義）：`sieve` 為單射且保 ∧、∨；
/// (·=1) 為格同態；(r=0)∧(r=1) = ⊥。回傳（面格大小, 篩數, 全部性質成立）。
pub fn verify_face_semantics(
  n : Int32,
  dm_universe : Array[Dm],
) -> (Int32, Int32, Bool) {
  let faces = face_lattice(n, limit=100000)
  let mut ok = true
  let sieves : Array[Array[Bool]] = []
  for x in faces {
    sieves.push(x.sieve(n))
  }
  for i in 0..<faces.length() {
    for j in 0..<faces.length() {
      if i != j && sieves[i] == sieves[j] {
        ok = false
      }
      let m = faces[i].meet(faces[j]).sieve(n)
      let u = faces[i].join(faces[j]).sieve(n)
      for c in 0..<m.length() {
        if m[c] != (sieves[i][c] && sieves[j][c]) {
          ok = false
        }
        if u[c] != (sieves[i][c] || sieves[j][c]) {
          ok = false
        }
      }
    }
  }
  for a in dm_universe {
    if !a.eq_zero().meet(a.eq_one()).same(Face::bot()) {
      ok = false
    }
    for b in dm_universe {
      if !a.meet(b).eq_one().same(a.eq_one().meet(b.eq_one())) {
        ok = false
      }
      if !a.join(b).eq_one().same(a.eq_one().join(b.eq_one())) {
        ok = false
      }
    }
  }
  (faces.length(), count_sieves(n), ok)
}
