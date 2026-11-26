-- ## Model checking: counterexample for `safe_retirement`
-- Breadth-first, so the trace is a shortest one. A violation is reported as
-- information, not as a build error.
set_option veil.violationIsError false in
#model_check interpreted { queue := Fin 2, req := Fin 2, num := Fin 3, val := fun n => n.val, qnum := fun q => q.val, maxIds := 2 }

end ApfAffectedMC
