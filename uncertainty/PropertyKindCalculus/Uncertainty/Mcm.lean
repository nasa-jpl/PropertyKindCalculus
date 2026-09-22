/-
`PropertyKindCalculus.Uncertainty.Mcm` — the Monte Carlo reference propagator.

MCM is the *reference* method of `UNCERTAINTY.md`: draw `n` joint samples of the inputs, push
each through the model, and report the sample mean and standard uncertainty of the output. It
makes no linearization and no independence-of-combination assumption (it samples the joint
directly), so it is the yardstick the cheaper methods (GUM, Willink, SSPRC) are validated
against. It is deliberately the simplest thing that works; efficiency is not its job.

The model is any `List Float → Float` — in practice a WO1 `[NumCarrier α]` kernel instantiated
at `Float`. Mathlib-free.
-/

module

public import PropertyKindCalculus.Uncertainty.InputDist

public section -- pkc-blanket
@[expose] section -- pkc-blanket-expose

namespace PropertyKindCalculus.Uncertainty.Mcm

open PropertyKindCalculus.Uncertainty

/-- Draw one sample from a distribution given a PRNG state; return `(sample, nextState)`. -/
def sampleOne (st : UInt64) (d : InputDist Float) : Float × UInt64 :=
  let (bits, st') := Sampling.next st
  (d.invCDF (Sampling.toUnit bits), st')

/-- **Monte Carlo propagation.** Returns `(E(Y), u(Y))` — the sample mean and (population)
standard deviation of `model` over `n` joint draws of `inputs`, seeded by `seed`. -/
def run (model : List Float → Float) (inputs : List (InputDist Float))
    (n : Nat) (seed : UInt64) : Float × Float := Id.run do
  let mut st := seed
  let mut sum : Float := 0.0
  let mut sumSq : Float := 0.0
  for _ in [0:n] do
    let mut xs : Array Float := #[]
    for d in inputs do
      let (x, st') := sampleOne st d
      st := st'
      xs := xs.push x
    let y := model xs.toList
    sum := sum + y
    sumSq := sumSq + y * y
  let nF := n.toFloat
  let mean := sum / nF
  let variance := sumSq / nF - mean * mean
  return (mean, Float.sqrt variance)

end PropertyKindCalculus.Uncertainty.Mcm

end -- pkc-blanket-expose
end -- pkc-blanket
