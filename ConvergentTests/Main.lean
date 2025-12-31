import Crucible
import ConvergentTests.CounterTests
import ConvergentTests.RegisterTests
import ConvergentTests.SetTests
import ConvergentTests.MapTests
import ConvergentTests.SequenceTests

open Crucible

def main : IO UInt32 := do
  IO.println "Convergent CRDT Tests"
  IO.println "====================="
  IO.println ""

  let result ← runAllSuites

  IO.println ""
  if result != 0 then
    IO.println "Some tests failed!"
  else
    IO.println "All tests passed!"

  return result
