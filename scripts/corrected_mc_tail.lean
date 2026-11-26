-- ## Exhaustive model checking (no maxDepth). Bounds and state counts are in
-- proof-status.md. `num := Fin k` gives widths and desired counts 1 .. k-1.
#model_check interpreted { queue := Fin 2, req := Fin 2, num := Fin 3, val := fun n => n.val, qnum := fun q => q.val, maxIds := 2 }
#model_check compiled { queue := Fin 3, req := Fin 3, num := Fin 4, val := fun n => n.val, qnum := fun q => q.val, maxIds := 3 }
#model_check compiled { queue := Fin 4, req := Fin 4, num := Fin 3, val := fun n => n.val, qnum := fun q => q.val, maxIds := 4 }

end ApfCorrectedMC
