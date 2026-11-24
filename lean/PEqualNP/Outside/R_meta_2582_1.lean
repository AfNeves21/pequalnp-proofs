import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_2582_1
    (hNorm : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      PEqualNP.TopForm.IsAO2 (N + N) C →
      (∀ z : Fin (N + N) → Bool,
        PEqualNP.MetaComplexity.circuitFun (N + N) C z =
          decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
            z (Fin.natAdd N l) = true)) →
      ∃ C' : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 (N + N) C' ∧
        (∀ z : Fin (N + N) → Bool,
          PEqualNP.MetaComplexity.circuitFun (N + N) C' z =
            decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
              z (Fin.natAdd N l) = true)) ∧
        C'.size ≤ C.size ∧
        (∀ i < C'.gates.length, ∀ j < C'.gates.length,
          (PEqualNP.MetaComplexity.NestedCover.gateAt C' i).op =
            PEqualNP.CircuitLowerBounds.GateOp.and →
          (∀ z : Fin (N + N) → Bool,
            PEqualNP.EdgeOwnership.gateVal (N + N) C' i z = true →
              ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
                z (Fin.natAdd N l) = true) →
          (PEqualNP.MetaComplexity.NestedCover.gateAt C' j).op =
            PEqualNP.CircuitLowerBounds.GateOp.and →
          ¬ PEqualNP.EdgeOwnership.InCone (N + N) C' i j))
    (hClean : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      PEqualNP.TopForm.IsAO2 (N + N) C →
      (∀ z : Fin (N + N) → Bool,
        PEqualNP.MetaComplexity.circuitFun (N + N) C z =
          decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
            z (Fin.natAdd N l) = true)) →
      (∀ i < C.gates.length, ∀ j < C.gates.length,
        (PEqualNP.MetaComplexity.NestedCover.gateAt C i).op =
          PEqualNP.CircuitLowerBounds.GateOp.and →
        (∀ z : Fin (N + N) → Bool,
          PEqualNP.EdgeOwnership.gateVal (N + N) C i z = true →
            ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
              z (Fin.natAdd N l) = true) →
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op =
          PEqualNP.CircuitLowerBounds.GateOp.and →
        ¬ PEqualNP.EdgeOwnership.InCone (N + N) C i j) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 (N + N) D ∧
        (∀ z : Fin (N + N) → Bool,
          PEqualNP.MetaComplexity.circuitFun (N + N) D z =
            decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
              z (Fin.natAdd N l) = true)) ∧
        D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (N + N) D 2) :
    ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      PEqualNP.TopForm.IsAO2 (N + N) C →
      (∀ z : Fin (N + N) → Bool,
        PEqualNP.MetaComplexity.circuitFun (N + N) C z =
          decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
            z (Fin.natAdd N l) = true)) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.TopForm.IsAO2 (N + N) D ∧
        (∀ z : Fin (N + N) → Bool,
          PEqualNP.MetaComplexity.circuitFun (N + N) D z =
            decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
              z (Fin.natAdd N l) = true)) ∧
        D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (N + N) D 2 := by
  intro q N I hI C hq hN hL hU hAO hfun
  obtain ⟨C', hAO', hfun', hsize', hnorm'⟩ :=
    hNorm q N I C hq hN hL hU hAO hfun
  obtain ⟨D, hD, hDfun, hDsize, hRead⟩ :=
    hClean q N I C' hq hN hL hU hAO' hfun' hnorm'
  exact ⟨D, hD, hDfun, le_trans hDsize hsize', hRead⟩
