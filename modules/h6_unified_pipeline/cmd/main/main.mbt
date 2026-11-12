///|
fn main {
  let audit = @h6.system_audit()
  println("== system audit ==")
  println(audit.render())
  println("audit certified: \{audit.certified()}")
  for entry in @h6.corpus() {
    let (title, src) = entry
    println("== \{title} ==")
    try @h6.run_pipeline(src, budget=20000, fuel=1000000) catch {
      err => println("error: " + err.message())
    } noraise {
      r => {
        println(r.render())
        println("certified: \{r.certified()}")
      }
    }
  }
  println("== round-two audit (S1..S10) ==")
  try @s10.round_two_audit() catch {
    err => println("error: \{err}")
  } noraise {
    items => {
      let mut passed = 0
      for it in items {
        let (name, detail, ok) = it
        if ok {
          passed += 1
        }
        println((if ok { "ok   " } else { "FAIL " }) + name + " — " + detail)
      }
      println("round-two audit: \{passed}/\{items.length()}")
    }
  }
}
