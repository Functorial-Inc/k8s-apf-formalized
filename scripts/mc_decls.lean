-- Model checking only: a complete list of requests, so that `conservation`
-- can be stated as a sum. For `req := Fin n` Veil resolves it to
-- `List.finRange n` (each request exactly once).
instantiate reqEnum : Veil.Enumeration req
-- Veil generates no verification conditions in the model-checking variants.
set_option veil.deferVCGeneration true
