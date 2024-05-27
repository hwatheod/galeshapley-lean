import GaleShapley.Compute.Basic

open GaleShapley.Compute

def mPrefTable2: List ((Fin 2) ≃ (Fin 2)) :=
  [
    List.Nodup.getEquivOfForallMemList [1, 0]  (by simp) (by intro; simp; omega),
    List.Nodup.getEquivOfForallMemList [0, 1]  (by simp) (by intro; simp; omega)
  ]

def wPrefTable2: List ((Fin 2) ≃ (Fin 2)) :=
  [
    List.Nodup.getEquivOfForallMemList [0, 1]  (by simp) (by intro; simp; omega),
    List.Nodup.getEquivOfForallMemList [0, 1]  (by simp) (by intro; simp; omega)
  ]

def mPrefTable4: List ((Fin 4) ≃ (Fin 4)) :=
  [
    List.Nodup.getEquivOfForallMemList [0, 1, 2, 3]  (by simp) (by intro; simp; omega),
    List.Nodup.getEquivOfForallMemList [0, 3, 2, 1]  (by simp) (by intro; simp; omega),
    List.Nodup.getEquivOfForallMemList [1, 0, 2, 3]  (by simp) (by intro; simp; omega),
    List.Nodup.getEquivOfForallMemList [3, 1, 2, 0]  (by simp) (by intro; simp; omega)
  ]

def wPrefTable4: List ((Fin 4) ≃ (Fin 4)) :=
  [
    List.Nodup.getEquivOfForallMemList [3, 2, 0, 1]  (by simp) (by intro; simp; omega),
    List.Nodup.getEquivOfForallMemList [1, 3, 0, 2]  (by simp) (by intro; simp; omega),
    List.Nodup.getEquivOfForallMemList [3, 0, 1, 2]  (by simp) (by intro; simp; omega),
    List.Nodup.getEquivOfForallMemList [2, 1, 0, 3]  (by simp) (by intro; simp; omega)
  ]

-- we can run a small case of size 2
abbrev M2 := Fin 2
abbrev W2 := Fin 2

def mPref2: Pref M2 W2 :=
  fun m => mPrefTable2[m]

def wPref2: Pref W2 M2 :=
  fun w => wPrefTable2[w]

#eval galeShapley mPref2 wPref2 0
#eval galeShapley mPref2 wPref2 1

def gs := galeShapley mPref2 wPref2
#eval isStableMatching mPref2 wPref2 gs
#eval isUnstablePair mPref2 wPref2 gs 1 1

-- for size 4
abbrev M4 := Fin 4
abbrev W4 := Fin 4

def mPref4: Pref M4 W4 :=
  fun m => mPrefTable4[m]

def wPref4: Pref W4 M4 :=
  fun w => wPrefTable4[w]

def example2_matching: Matching M4 W4 := {
  matching := fun m => match m.val with
    | 0 => some 2
    | 1 => some 3
    | 2 => some 0
    | 3 => some 1
    | _ => none
  matchingCondition := by
    simp [isMatching]
    intro m1 m2 w
    split <;> simp <;> split <;> simp <;>
      (intro; apply_fun (fun x => x.val); simp; omega; exact Fin.val_injective)
}

#eval isStableMatching mPref4 wPref4 example2_matching

-- modifying the matching from example 2 to get an unstable matching
def example2_matching': Matching M4 W4 := {
  matching := fun m => match m.val with
    | 0 => some 2
    | 1 => some 0
    | 2 => some 3
    | 3 => some 1
    | _ => none
  matchingCondition := by
    simp [isMatching]
    intro m1 m2 w
    split <;> simp <;> split <;> simp <;>
      (intro; apply_fun (fun x => x.val); simp; omega; exact Fin.val_injective)
}

#eval isStableMatching mPref4 wPref4 example2_matching'

-- For BasicAlt, the n=4 case is too slow to run for some reason.
#eval galeShapley mPref4 wPref4 0

-- main function for the 4 case.
def main : IO Unit := do
  let gs := galeShapley mPref4 wPref4
  IO.println (gs 0)
  IO.println (gs 1)
  IO.println (gs 2)
  IO.println (gs 3)
