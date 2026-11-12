///|
/// 證明即程式：抹除類型後的可執行碼（無類型 λ-項，綁定結構與核心項一致）。
#derive(Eq)
pub(all) enum Code {
  CVar(Int32)
  CLam(Code)
  CApp(Code, Code)
  CPair(Code, Code)
  CFst(Code)
  CSnd(Code)
  CStar
  CTt
  CFf
  CIf(Code, Code, Code)
  CZero
  CSucc(Code)
  /// CRec(z, s, n)：s 綁定 2 個變數
  CRec(Code, Code, Code)
  CRefl(Code)
  /// CJ(d, p)：d 綁定 1 個變數
  CJ(Code, Code)
  CAbsurd(Code)
  /// 被抹除的類型層內容（無計算意義）
  CBox
}

///|
pub extend Code with Eq::{equal, not_equal}

///|
pub fn code_size(c : Code) -> Int32 {
  match c {
    CVar(_) | CStar | CTt | CFf | CZero | CBox => 1
    CLam(b) | CFst(b) | CSnd(b) | CSucc(b) | CRefl(b) | CAbsurd(b) =>
      1 + code_size(b)
    CApp(a, b) | CPair(a, b) | CJ(a, b) => 1 + code_size(a) + code_size(b)
    CIf(a, b, d) | CRec(a, b, d) =>
      1 + code_size(a) + code_size(b) + code_size(d)
  }
}

///|
/// 由推導樹抽取程式：類型為宇宙的子推導（即類型本身）整體抹除為 CBox，
/// 動機、定義域標註與纖維族不進入程式；其餘依規則結構逐一對應。
pub fn extract(d : Deriv) -> Code {
  if d.ty is VUniv(_) {
    return CBox
  }
  let ps = d.premises
  match (d.rule, d.tm) {
    (Conv, _) => extract(ps[0])
    (Hyp, Var(i)) => CVar(i)
    (PiI, _) => CLam(extract(ps[1]))
    (PiE, _) => CApp(extract(ps[0]), extract(ps[1]))
    (SigmaI, _) => CPair(extract(ps[0]), extract(ps[2]))
    (SigmaE1, _) => CFst(extract(ps[0]))
    (SigmaE2, _) => CSnd(extract(ps[0]))
    (UnitI, _) => CStar
    (EmptyE, _) => CAbsurd(extract(ps[1]))
    (BoolI, Tt) => CTt
    (BoolI, _) => CFf
    (BoolE, _) => CIf(extract(ps[1]), extract(ps[2]), extract(ps[3]))
    (NatI, Zero) => CZero
    (NatI, _) => CSucc(extract(ps[0]))
    (NatE, _) => CRec(extract(ps[1]), extract(ps[2]), extract(ps[3]))
    (IdI, _) => CRefl(extract(ps[0]))
    (IdE, _) => CJ(extract(ps[1]), extract(ps[2]))
    _ => CBox
  }
}

///|
/// 機器值（弱頭正規形）。
pub(all) enum MVal {
  MLam(Code, MEnv)
  MPair(Cell, Cell)
  MStar
  MTt
  MFf
  MZero
  MSucc(Cell)
  MRefl(Cell)
  MBox
}

///|
pub(all) enum MSusp {
  MDone(MVal)
  MDelay(Code, MEnv)
  /// 遞迴的歸納假設 rec(z, s, pred)
  MRecIH(Code, Code, MEnv, Cell)
  /// 求值中（重入即為無窮迴圈）
  MBlackhole
}

///|
/// 堆積單元：call-by-need 的更新目標。
pub(all) struct Cell {
  mut s : MSusp
}

///|
pub(all) enum MEnv {
  MNil
  MCons(Cell, MEnv)
}

///|
priv enum Frame {
  FArg(Cell)
  FUpdate(Cell)
  FFst
  FSnd
  FIf(Code, Code, MEnv)
  FRec(Code, Code, MEnv)
  FJ(Code, MEnv)
  FAbsurd
}

///|
priv enum Ctrl {
  Eval(Code, MEnv)
  Enter(Cell)
  Ret(MVal)
}

///|
/// 惰性抽象機（Krivine 機 + 更新標記；顯式堆疊、無宿主遞迴）。
pub(all) struct Machine {
  /// 狀態轉移總數
  mut steps : Int32
  /// 堆積配置數／記憶化更新數／堆疊高水位
  mut allocs : Int32
  mut updates : Int32
  mut max_stack : Int32
  fuel : Int32
}

///|
pub fn Machine::new(fuel~ : Int32) -> Machine {
  { steps: 0, allocs: 0, updates: 0, max_stack: 0, fuel, }
}

///|
fn mlookup(env : MEnv, i : Int32) -> Cell raise KernelError {
  let mut cur = env
  let mut k = i
  while true {
    match cur {
      MNil => raise Unbound(i)
      MCons(c, rest) => {
        if k == 0 {
          return c
        }
        k -= 1
        cur = rest
      }
    }
  }
  raise Unbound(i)
}

///|
fn Machine::alloc(
  self : Machine,
  c : Code,
  env : MEnv,
) -> Cell raise KernelError {
  match c {
    CVar(i) => mlookup(env, i)
    _ => {
      self.allocs += 1
      { s: MDelay(c, env), }
    }
  }
}

///|
/// 執行閉項程式至弱頭正規形。
pub fn Machine::run(self : Machine, code : Code) -> MVal raise KernelError {
  self.drive(Eval(code, MNil))
}

///|
/// 強制一個堆積單元。
pub fn Machine::force(self : Machine, cell : Cell) -> MVal raise KernelError {
  self.drive(Enter(cell))
}

///|
fn Machine::drive(self : Machine, start : Ctrl) -> MVal raise KernelError {
  let stack : Array[Frame] = []
  let mut ctrl = start
  while true {
    self.steps += 1
    if self.steps > self.fuel {
      raise Fuel(self.steps)
    }
    if stack.length() > self.max_stack {
      self.max_stack = stack.length()
    }
    match ctrl {
      Eval(c, env) =>
        match c {
          CVar(i) => ctrl = Enter(mlookup(env, i))
          CLam(b) => ctrl = Ret(MLam(b, env))
          CApp(f, a) => {
            stack.push(FArg(self.alloc(a, env)))
            ctrl = Eval(f, env)
          }
          CPair(a, b) => {
            let ca = self.alloc(a, env)
            ctrl = Ret(MPair(ca, self.alloc(b, env)))
          }
          CFst(p) => {
            stack.push(FFst)
            ctrl = Eval(p, env)
          }
          CSnd(p) => {
            stack.push(FSnd)
            ctrl = Eval(p, env)
          }
          CStar => ctrl = Ret(MStar)
          CTt => ctrl = Ret(MTt)
          CFf => ctrl = Ret(MFf)
          CIf(s, x, y) => {
            stack.push(FIf(x, y, env))
            ctrl = Eval(s, env)
          }
          CZero => ctrl = Ret(MZero)
          CSucc(n) => ctrl = Ret(MSucc(self.alloc(n, env)))
          CRec(z, s, n) => {
            stack.push(FRec(z, s, env))
            ctrl = Eval(n, env)
          }
          CRefl(a) => ctrl = Ret(MRefl(self.alloc(a, env)))
          CJ(d, p) => {
            stack.push(FJ(d, env))
            ctrl = Eval(p, env)
          }
          CAbsurd(e) => {
            stack.push(FAbsurd)
            ctrl = Eval(e, env)
          }
          CBox => ctrl = Ret(MBox)
        }
      Enter(cell) =>
        match cell.s {
          MDone(v) => ctrl = Ret(v)
          MDelay(c, env) => {
            cell.s = MBlackhole
            stack.push(FUpdate(cell))
            ctrl = Eval(c, env)
          }
          MRecIH(z, s, env, pred) => {
            cell.s = MBlackhole
            stack.push(FUpdate(cell))
            stack.push(FRec(z, s, env))
            ctrl = Enter(pred)
          }
          MBlackhole => raise Stuck("black hole: a thunk depends on itself")
        }
      Ret(v) =>
        match stack.pop() {
          None => return v
          Some(FUpdate(cell)) => {
            cell.s = MDone(v)
            self.updates += 1
          }
          Some(FArg(cell)) =>
            match v {
              MLam(b, env) => ctrl = Eval(b, MCons(cell, env))
              _ => raise Stuck("machine: application of a non-function")
            }
          Some(FFst) =>
            match v {
              MPair(a, _) => ctrl = Enter(a)
              _ => raise Stuck("machine: fst of a non-pair")
            }
          Some(FSnd) =>
            match v {
              MPair(_, b) => ctrl = Enter(b)
              _ => raise Stuck("machine: snd of a non-pair")
            }
          Some(FIf(x, y, env)) =>
            match v {
              MTt => ctrl = Eval(x, env)
              MFf => ctrl = Eval(y, env)
              _ => raise Stuck("machine: if on a non-boolean")
            }
          Some(FRec(z, s, env)) =>
            match v {
              MZero => ctrl = Eval(z, env)
              MSucc(pred) => {
                self.allocs += 1
                let ih : Cell = { s: MRecIH(z, s, env, pred), }
                ctrl = Eval(s, MCons(ih, MCons(pred, env)))
              }
              _ => raise Stuck("machine: rec on a non-numeral")
            }
          Some(FJ(d, env)) =>
            match v {
              MRefl(a) => ctrl = Eval(d, MCons(a, env))
              _ => raise Stuck("machine: J on a non-refl")
            }
          Some(FAbsurd) => raise Stuck("machine: absurd received a value")
        }
    }
  }
  raise Stuck("machine: unreachable")
}

///|
/// 將數字值完全強制並讀回為整數（逐一強制後繼鏈，不使用宿主遞迴）。
pub fn Machine::read_nat(self : Machine, v : MVal) -> Int32 raise KernelError {
  let mut cur = v
  let mut n = 0
  while true {
    match cur {
      MZero => return n
      MSucc(cell) => {
        n += 1
        cur = self.force(cell)
      }
      _ => raise Expected("a numeral", "another machine value")
    }
  }
  n
}

///|
/// 深度強制並讀回為可讀字串（數字、布林、序對、star；函數與類型以佔位符表示）。
pub fn Machine::readback(self : Machine, v : MVal) -> String raise KernelError {
  match v {
    MZero | MSucc(_) => "\{self.read_nat(v)}"
    MTt => "tt"
    MFf => "ff"
    MStar => "star"
    MPair(a, b) => {
      let x = self.readback(self.force(a))
      let y = self.readback(self.force(b))
      "(pair \{x} \{y})"
    }
    MRefl(_) => "refl"
    MLam(_, _) => "<fun>"
    MBox => "<type>"
  }
}
