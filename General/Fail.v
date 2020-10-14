Function lift {X P} (s : @sig X P) : X :=
  match s with exist _ x pf => x end.