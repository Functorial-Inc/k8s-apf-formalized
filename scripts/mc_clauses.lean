-- ## Model checking only: checked in every reachable state
-- `conservation_fo` is the formula that the unbounded proof (Corrected.lean)
-- assumes in `release`; here it is checked, not assumed.
safety [conservation_fo]
  (phase R1 = executing ∨ phase R1 = lingering) ∧
  (phase R2 = executing ∨ phase R2 = lingering) ∧
  R1 ≠ R2 ∧ rq R1 = rq R2 →
    (width R1 : Int) + (width R2 : Int) ≤ seatsInUse (rq R1)
-- `conservation` (docs/model-contract.md), sum form and nonnegativity.
safety [conservation]
  seatsInUse Q = ((Veil.Enumeration.allValues : List req).map (fun r =>
    if (phase r = executing ∨ phase r = lingering) ∧ rq r = Q then (width r : Int) else 0)).sum ∧
  totSeats = ((Veil.Enumeration.allValues : List req).map (fun r =>
    if phase r = executing ∨ phase r = lingering then (width r : Int) else 0)).sum ∧
  (0 : Int) ≤ seatsInUse Q ∧ (0 : Int) ≤ totSeats
