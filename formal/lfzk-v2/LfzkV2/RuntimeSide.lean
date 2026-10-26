import LfzkV2.CompiledSide
import LfzkV2.RuntimeProfiles

/-! Attach a checked numerical profile to the actual compiled side. This
changes its analysis-side witness list and potential, while preserving its
compiled statement and verifier. -/

namespace LfzkV2

open RecursivePolygero Finset
open scoped Classical

namespace RuntimeProfiles

variable {F C : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype C]

structure Geometry (p : Profile) (I : Instance F) : Prop where
  n : I.n = p.n
  k : I.r+I.w = p.k
  s : I.s = p.s
  t : I.t = p.t

structure BackendSampling (I : Instance F)
    (decodeCoin : C → I.layer.Coin) (decodeQuery : C → I.layer.Query) where
  kCoin : ℕ
  kQuery : ℕ
  coin_bound : ∀ coin, (univ.filter fun c : C => decodeCoin c = coin).card ≤ kCoin
  query_bound : ∀ query, (univ.filter fun c : C => decodeQuery c = query).card ≤ kQuery
  coin_balanced : kCoin*Fintype.card I.layer.Coin ≤ Fintype.card C
  query_balanced : kQuery*Fintype.card I.layer.Query ≤ Fintype.card C

end RuntimeProfiles

namespace CompiledSide

variable {F C Context : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype C]
variable {out input : ℕ} {circuit : Circuit F out input} {I : Instance F}
variable (S : CompiledSide F C Context circuit I) (p : RuntimeProfiles.Profile)
variable (geometry : RuntimeProfiles.Geometry p I)
variable (sampling : RuntimeProfiles.BackendSampling I S.decodeCoin S.decodeQuery)

noncomputable def withProfile : CompiledSide F C Context circuit I :=
  { S with
    cutoff := p.cutoff
    bound := p.candidates
    cutoff_gt := by simpa only [geometry.k] using p.cutoff_gt
    packing := p.committedPacking_instance I geometry.n geometry.k
    potential := p.potential I geometry.n geometry.k geometry.s geometry.t S.decodeCoin S.decodeQuery
      sampling.kCoin sampling.kQuery sampling.coin_bound sampling.query_bound }

theorem withProfile_statement (ctx : Context) (v : Reconstruction circuit S.Pad S.Slot) :
    (withProfile S p geometry sampling).statement ctx v = S.statement ctx v := rfl

theorem withProfile_inputOf (ctx : Context) (g : (Counting.tupleCounts I).Index) :
    (withProfile S p geometry sampling).inputOf ctx g = S.inputOf ctx g := rfl

/-- The profiled side uses the same actual opening-only verifier. -/
theorem withProfile_accepts {Parent : Type} (keyOf : Parent → Context)
    (payloadOf : Parent → Replay.Payload circuit) (W : I.layer.Oracle)
    (H : ConcreteFS.Domain Context circuit I Parent → C) (selected : Parent × I.layer.Payload) :
    (withProfile S p geometry sampling).Accepts keyOf payloadOf W H selected ↔
      S.Accepts keyOf payloadOf W H selected := Iff.rfl

theorem withProfile_budgets_le [Nonempty C] (hfield : p.minimumField ≤ Nat.card F) :
    let T := withProfile S p geometry sampling
    T.potential.challengeBudget/Fintype.card C ≤ (p.capacities+1 : ℕ)/(p.minimumField : ℚ) ∧
      T.potential.queryBudget/Fintype.card C ≤ p.queryUnits/(2^128 : ℚ) :=
  p.potential_budgets_le I geometry.n geometry.k geometry.s geometry.t hfield S.decodeCoin S.decodeQuery
    sampling.kCoin sampling.kQuery sampling.coin_bound sampling.query_bound sampling.coin_balanced sampling.query_balanced

end CompiledSide
end LfzkV2
