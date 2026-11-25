import PEqualNP.Defs.ProofComplexityBit

-- Five pigeons are encoded by two bits each. The forty input clauses forbid
-- each of the ten unordered pairs from sharing any of the four bit patterns.
-- For line n, ln is the clause, pn the newest-first prefix, and dn its derivation.
namespace BinaryFiveCertificate
open PEqualNP.ProofComplexity
abbrev V := Fin 5 × Fin 2
abbrev LC := LinClause V
abbrev F := ((fun C => linOfClause C) '' BPHP 5 2)
def inputClause (i j : Fin 5) (h : Nat) : Clause V :=
  Finset.univ.image (fun b : Fin 2 => ((i,b), !h.testBit b.val)) ∪
    Finset.univ.image (fun b : Fin 2 => ((j,b), !h.testBit b.val))
theorem inputMem (i j : Fin 5) (h : Nat) (hd : i ≠ j) : linOfClause (inputClause i j h) ∈ F :=
  ⟨inputClause i j h, ⟨i, j, fun b => h.testBit b.val, hd, rfl⟩, rfl⟩
theorem lineAt (l : List LC) (k : Nat) (h : k < l.length) : l[k] ∈ l := List.getElem_mem h

def l0 : LC := linOfClause (inputClause 0 1 0)
def p0 : List LC := l0 :: []
theorem d0 : IsLinDerivation F p0 :=
  IsLinDerivation.ax IsLinDerivation.nil (inputMem 0 1 0 (by decide))

def l1 : LC := linOfClause (inputClause 0 1 1)
def p1 : List LC := l1 :: p0
theorem d1 : IsLinDerivation F p1 :=
  IsLinDerivation.ax d0 (inputMem 0 1 1 (by decide))

def l2 : LC := linOfClause (inputClause 0 1 2)
def p2 : List LC := l2 :: p1
theorem d2 : IsLinDerivation F p2 :=
  IsLinDerivation.ax d1 (inputMem 0 1 2 (by decide))

def l3 : LC := linOfClause (inputClause 0 1 3)
def p3 : List LC := l3 :: p2
theorem d3 : IsLinDerivation F p3 :=
  IsLinDerivation.ax d2 (inputMem 0 1 3 (by decide))

def l4 : LC := linOfClause (inputClause 0 2 0)
def p4 : List LC := l4 :: p3
theorem d4 : IsLinDerivation F p4 :=
  IsLinDerivation.ax d3 (inputMem 0 2 0 (by decide))

def l5 : LC := linOfClause (inputClause 0 2 1)
def p5 : List LC := l5 :: p4
theorem d5 : IsLinDerivation F p5 :=
  IsLinDerivation.ax d4 (inputMem 0 2 1 (by decide))

def l6 : LC := linOfClause (inputClause 0 2 2)
def p6 : List LC := l6 :: p5
theorem d6 : IsLinDerivation F p6 :=
  IsLinDerivation.ax d5 (inputMem 0 2 2 (by decide))

def l7 : LC := linOfClause (inputClause 0 2 3)
def p7 : List LC := l7 :: p6
theorem d7 : IsLinDerivation F p7 :=
  IsLinDerivation.ax d6 (inputMem 0 2 3 (by decide))

def l8 : LC := linOfClause (inputClause 0 3 0)
def p8 : List LC := l8 :: p7
theorem d8 : IsLinDerivation F p8 :=
  IsLinDerivation.ax d7 (inputMem 0 3 0 (by decide))

def l9 : LC := linOfClause (inputClause 0 3 1)
def p9 : List LC := l9 :: p8
theorem d9 : IsLinDerivation F p9 :=
  IsLinDerivation.ax d8 (inputMem 0 3 1 (by decide))

def l10 : LC := linOfClause (inputClause 0 3 2)
def p10 : List LC := l10 :: p9
theorem d10 : IsLinDerivation F p10 :=
  IsLinDerivation.ax d9 (inputMem 0 3 2 (by decide))

def l11 : LC := linOfClause (inputClause 0 3 3)
def p11 : List LC := l11 :: p10
theorem d11 : IsLinDerivation F p11 :=
  IsLinDerivation.ax d10 (inputMem 0 3 3 (by decide))

def l12 : LC := linOfClause (inputClause 0 4 0)
def p12 : List LC := l12 :: p11
theorem d12 : IsLinDerivation F p12 :=
  IsLinDerivation.ax d11 (inputMem 0 4 0 (by decide))

def l13 : LC := linOfClause (inputClause 0 4 1)
def p13 : List LC := l13 :: p12
theorem d13 : IsLinDerivation F p13 :=
  IsLinDerivation.ax d12 (inputMem 0 4 1 (by decide))

def l14 : LC := linOfClause (inputClause 0 4 2)
def p14 : List LC := l14 :: p13
theorem d14 : IsLinDerivation F p14 :=
  IsLinDerivation.ax d13 (inputMem 0 4 2 (by decide))

def l15 : LC := linOfClause (inputClause 0 4 3)
def p15 : List LC := l15 :: p14
theorem d15 : IsLinDerivation F p15 :=
  IsLinDerivation.ax d14 (inputMem 0 4 3 (by decide))

def l16 : LC := linOfClause (inputClause 1 2 0)
def p16 : List LC := l16 :: p15
theorem d16 : IsLinDerivation F p16 :=
  IsLinDerivation.ax d15 (inputMem 1 2 0 (by decide))

def l17 : LC := linOfClause (inputClause 1 2 1)
def p17 : List LC := l17 :: p16
theorem d17 : IsLinDerivation F p17 :=
  IsLinDerivation.ax d16 (inputMem 1 2 1 (by decide))

def l18 : LC := linOfClause (inputClause 1 2 2)
def p18 : List LC := l18 :: p17
theorem d18 : IsLinDerivation F p18 :=
  IsLinDerivation.ax d17 (inputMem 1 2 2 (by decide))

def l19 : LC := linOfClause (inputClause 1 2 3)
def p19 : List LC := l19 :: p18
theorem d19 : IsLinDerivation F p19 :=
  IsLinDerivation.ax d18 (inputMem 1 2 3 (by decide))

def l20 : LC := linOfClause (inputClause 1 3 0)
def p20 : List LC := l20 :: p19
theorem d20 : IsLinDerivation F p20 :=
  IsLinDerivation.ax d19 (inputMem 1 3 0 (by decide))

def l21 : LC := linOfClause (inputClause 1 3 1)
def p21 : List LC := l21 :: p20
theorem d21 : IsLinDerivation F p21 :=
  IsLinDerivation.ax d20 (inputMem 1 3 1 (by decide))

def l22 : LC := linOfClause (inputClause 1 3 2)
def p22 : List LC := l22 :: p21
theorem d22 : IsLinDerivation F p22 :=
  IsLinDerivation.ax d21 (inputMem 1 3 2 (by decide))

def l23 : LC := linOfClause (inputClause 1 3 3)
def p23 : List LC := l23 :: p22
theorem d23 : IsLinDerivation F p23 :=
  IsLinDerivation.ax d22 (inputMem 1 3 3 (by decide))

def l24 : LC := linOfClause (inputClause 1 4 0)
def p24 : List LC := l24 :: p23
theorem d24 : IsLinDerivation F p24 :=
  IsLinDerivation.ax d23 (inputMem 1 4 0 (by decide))

def l25 : LC := linOfClause (inputClause 1 4 1)
def p25 : List LC := l25 :: p24
theorem d25 : IsLinDerivation F p25 :=
  IsLinDerivation.ax d24 (inputMem 1 4 1 (by decide))

def l26 : LC := linOfClause (inputClause 1 4 2)
def p26 : List LC := l26 :: p25
theorem d26 : IsLinDerivation F p26 :=
  IsLinDerivation.ax d25 (inputMem 1 4 2 (by decide))

def l27 : LC := linOfClause (inputClause 1 4 3)
def p27 : List LC := l27 :: p26
theorem d27 : IsLinDerivation F p27 :=
  IsLinDerivation.ax d26 (inputMem 1 4 3 (by decide))

def l28 : LC := linOfClause (inputClause 2 3 0)
def p28 : List LC := l28 :: p27
theorem d28 : IsLinDerivation F p28 :=
  IsLinDerivation.ax d27 (inputMem 2 3 0 (by decide))

def l29 : LC := linOfClause (inputClause 2 3 1)
def p29 : List LC := l29 :: p28
theorem d29 : IsLinDerivation F p29 :=
  IsLinDerivation.ax d28 (inputMem 2 3 1 (by decide))

def l30 : LC := linOfClause (inputClause 2 3 2)
def p30 : List LC := l30 :: p29
theorem d30 : IsLinDerivation F p30 :=
  IsLinDerivation.ax d29 (inputMem 2 3 2 (by decide))

def l31 : LC := linOfClause (inputClause 2 3 3)
def p31 : List LC := l31 :: p30
theorem d31 : IsLinDerivation F p31 :=
  IsLinDerivation.ax d30 (inputMem 2 3 3 (by decide))

def l32 : LC := linOfClause (inputClause 2 4 0)
def p32 : List LC := l32 :: p31
theorem d32 : IsLinDerivation F p32 :=
  IsLinDerivation.ax d31 (inputMem 2 4 0 (by decide))

def l33 : LC := linOfClause (inputClause 2 4 1)
def p33 : List LC := l33 :: p32
theorem d33 : IsLinDerivation F p33 :=
  IsLinDerivation.ax d32 (inputMem 2 4 1 (by decide))

def l34 : LC := linOfClause (inputClause 2 4 2)
def p34 : List LC := l34 :: p33
theorem d34 : IsLinDerivation F p34 :=
  IsLinDerivation.ax d33 (inputMem 2 4 2 (by decide))

def l35 : LC := linOfClause (inputClause 2 4 3)
def p35 : List LC := l35 :: p34
theorem d35 : IsLinDerivation F p35 :=
  IsLinDerivation.ax d34 (inputMem 2 4 3 (by decide))

def l36 : LC := linOfClause (inputClause 3 4 0)
def p36 : List LC := l36 :: p35
theorem d36 : IsLinDerivation F p36 :=
  IsLinDerivation.ax d35 (inputMem 3 4 0 (by decide))

def l37 : LC := linOfClause (inputClause 3 4 1)
def p37 : List LC := l37 :: p36
theorem d37 : IsLinDerivation F p37 :=
  IsLinDerivation.ax d36 (inputMem 3 4 1 (by decide))

def l38 : LC := linOfClause (inputClause 3 4 2)
def p38 : List LC := l38 :: p37
theorem d38 : IsLinDerivation F p38 :=
  IsLinDerivation.ax d37 (inputMem 3 4 2 (by decide))

def l39 : LC := linOfClause (inputClause 3 4 3)
def p39 : List LC := l39 :: p38
theorem d39 : IsLinDerivation F p39 :=
  IsLinDerivation.ax d38 (inputMem 3 4 3 (by decide))

-- Lines 40 through 148 resolve earlier clauses. The last clause is empty.
def l40 : LC := {(({(1,0)} : Finset V),false),(({(1,1)} : Finset V),true),(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),false),(({(3,0)} : Finset V),false)}
def p40 : List LC := l40 :: p39
theorem d40 : IsLinDerivation F p40 :=
  IsLinDerivation.res (C := l31) (D := l21) d39
    (lineAt p39 8 (by decide +kernel)) (lineAt p39 18 (by decide +kernel))
    ⟨({(3,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l41 : LC := {(({(1,0)} : Finset V),false),(({(1,1)} : Finset V),true),(({(2,0)} : Finset V),false),(({(3,0)} : Finset V),false)}
def p41 : List LC := l41 :: p40
theorem d41 : IsLinDerivation F p41 :=
  IsLinDerivation.res (C := l40) (D := l17) d40
    (lineAt p40 0 (by decide +kernel)) (lineAt p40 23 (by decide +kernel))
    ⟨({(2,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l42 : LC := {(({(0,0)} : Finset V),false),(({(0,1)} : Finset V),false),(({(3,0)} : Finset V),false),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),true)}
def p42 : List LC := l42 :: p41
theorem d42 : IsLinDerivation F p42 :=
  IsLinDerivation.res (C := l11) (D := l37) d41
    (lineAt p41 30 (by decide +kernel)) (lineAt p41 4 (by decide +kernel))
    ⟨({(3,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l43 : LC := {(({(0,0)} : Finset V),true),(({(0,1)} : Finset V),true),(({(1,0)} : Finset V),true),(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),false)}
def p43 : List LC := l43 :: p42
theorem d43 : IsLinDerivation F p43 :=
  IsLinDerivation.res (C := l18) (D := l0) d42
    (lineAt p42 24 (by decide +kernel)) (lineAt p42 42 (by decide +kernel))
    ⟨({(1,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l44 : LC := {(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),true),(({(3,0)} : Finset V),false),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),false)}
def p44 : List LC := l44 :: p43
theorem d44 : IsLinDerivation F p44 :=
  IsLinDerivation.res (C := l39) (D := l29) d43
    (lineAt p43 4 (by decide +kernel)) (lineAt p43 14 (by decide +kernel))
    ⟨({(3,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l45 : LC := {(({(1,0)} : Finset V),false),(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),true),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),false)}
def p45 : List LC := l45 :: p44
theorem d45 : IsLinDerivation F p45 :=
  IsLinDerivation.res (C := l27) (D := l17) d44
    (lineAt p44 17 (by decide +kernel)) (lineAt p44 27 (by decide +kernel))
    ⟨({(1,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l46 : LC := {(({(0,0)} : Finset V),true),(({(0,1)} : Finset V),false),(({(1,0)} : Finset V),true),(({(3,0)} : Finset V),true),(({(3,1)} : Finset V),true)}
def p46 : List LC := l46 :: p45
theorem d46 : IsLinDerivation F p46 :=
  IsLinDerivation.res (C := l2) (D := l20) d45
    (lineAt p45 43 (by decide +kernel)) (lineAt p45 25 (by decide +kernel))
    ⟨({(1,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l47 : LC := {(({(0,0)} : Finset V),true),(({(0,1)} : Finset V),false),(({(1,0)} : Finset V),true),(({(3,0)} : Finset V),true)}
def p47 : List LC := l47 :: p46
theorem d47 : IsLinDerivation F p47 :=
  IsLinDerivation.res (C := l10) (D := l46) d46
    (lineAt p46 36 (by decide +kernel)) (lineAt p46 0 (by decide +kernel))
    ⟨({(3,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l48 : LC := {(({(1,0)} : Finset V),true),(({(1,1)} : Finset V),false),(({(2,0)} : Finset V),true),(({(3,0)} : Finset V),true),(({(3,1)} : Finset V),true)}
def p48 : List LC := l48 :: p47
theorem d48 : IsLinDerivation F p48 :=
  IsLinDerivation.res (C := l18) (D := l28) d47
    (lineAt p47 29 (by decide +kernel)) (lineAt p47 19 (by decide +kernel))
    ⟨({(2,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l49 : LC := {(({(1,0)} : Finset V),true),(({(2,0)} : Finset V),true),(({(3,0)} : Finset V),true),(({(3,1)} : Finset V),true)}
def p49 : List LC := l49 :: p48
theorem d49 : IsLinDerivation F p49 :=
  IsLinDerivation.res (C := l48) (D := l20) d48
    (lineAt p48 0 (by decide +kernel)) (lineAt p48 28 (by decide +kernel))
    ⟨({(1,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l50 : LC := {(({(1,0)} : Finset V),false),(({(1,1)} : Finset V),false),(({(3,0)} : Finset V),false),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),true)}
def p50 : List LC := l50 :: p49
theorem d50 : IsLinDerivation F p50 :=
  IsLinDerivation.res (C := l23) (D := l37) d49
    (lineAt p49 26 (by decide +kernel)) (lineAt p49 12 (by decide +kernel))
    ⟨({(3,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l51 : LC := {(({(1,0)} : Finset V),false),(({(3,0)} : Finset V),false),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),true)}
def p51 : List LC := l51 :: p50
theorem d51 : IsLinDerivation F p51 :=
  IsLinDerivation.res (C := l50) (D := l25) d50
    (lineAt p50 0 (by decide +kernel)) (lineAt p50 25 (by decide +kernel))
    ⟨({(1,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l52 : LC := {(({(2,0)} : Finset V),true),(({(3,0)} : Finset V),true),(({(3,1)} : Finset V),false),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),true)}
def p52 : List LC := l52 :: p51
theorem d52 : IsLinDerivation F p52 :=
  IsLinDerivation.res (C := l30) (D := l32) d51
    (lineAt p51 21 (by decide +kernel)) (lineAt p51 19 (by decide +kernel))
    ⟨({(2,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l53 : LC := {(({(1,0)} : Finset V),false),(({(3,0)} : Finset V),false),(({(3,1)} : Finset V),true),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),false)}
def p53 : List LC := l53 :: p52
theorem d53 : IsLinDerivation F p53 :=
  IsLinDerivation.res (C := l27) (D := l21) d52
    (lineAt p52 25 (by decide +kernel)) (lineAt p52 31 (by decide +kernel))
    ⟨({(1,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l54 : LC := {(({(1,0)} : Finset V),false),(({(3,0)} : Finset V),false),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),false)}
def p54 : List LC := l54 :: p53
theorem d54 : IsLinDerivation F p54 :=
  IsLinDerivation.res (C := l39) (D := l53) d53
    (lineAt p53 14 (by decide +kernel)) (lineAt p53 0 (by decide +kernel))
    ⟨({(3,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l55 : LC := {(({(1,0)} : Finset V),false),(({(3,0)} : Finset V),false),(({(4,0)} : Finset V),false)}
def p55 : List LC := l55 :: p54
theorem d55 : IsLinDerivation F p55 :=
  IsLinDerivation.res (C := l54) (D := l51) d54
    (lineAt p54 0 (by decide +kernel)) (lineAt p54 3 (by decide +kernel))
    ⟨({(4,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l56 : LC := {(({(1,0)} : Finset V),false),(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),false),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),true)}
def p56 : List LC := l56 :: p55
theorem d56 : IsLinDerivation F p56 :=
  IsLinDerivation.res (C := l19) (D := l25) d55
    (lineAt p55 36 (by decide +kernel)) (lineAt p55 30 (by decide +kernel))
    ⟨({(1,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l57 : LC := {(({(1,0)} : Finset V),false),(({(1,1)} : Finset V),false),(({(2,0)} : Finset V),false),(({(3,0)} : Finset V),false),(({(3,1)} : Finset V),true)}
def p57 : List LC := l57 :: p56
theorem d57 : IsLinDerivation F p57 :=
  IsLinDerivation.res (C := l19) (D := l29) d56
    (lineAt p56 37 (by decide +kernel)) (lineAt p56 27 (by decide +kernel))
    ⟨({(2,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l58 : LC := {(({(1,0)} : Finset V),false),(({(1,1)} : Finset V),false),(({(2,0)} : Finset V),false),(({(3,0)} : Finset V),false)}
def p58 : List LC := l58 :: p57
theorem d58 : IsLinDerivation F p58 :=
  IsLinDerivation.res (C := l23) (D := l57) d57
    (lineAt p57 34 (by decide +kernel)) (lineAt p57 0 (by decide +kernel))
    ⟨({(3,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l59 : LC := {(({(1,0)} : Finset V),false),(({(2,0)} : Finset V),false),(({(3,0)} : Finset V),false)}
def p59 : List LC := l59 :: p58
theorem d59 : IsLinDerivation F p59 :=
  IsLinDerivation.res (C := l58) (D := l41) d58
    (lineAt p58 0 (by decide +kernel)) (lineAt p58 17 (by decide +kernel))
    ⟨({(1,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l60 : LC := {(({(0,0)} : Finset V),true),(({(0,1)} : Finset V),true),(({(1,0)} : Finset V),true),(({(1,1)} : Finset V),false),(({(3,0)} : Finset V),true)}
def p60 : List LC := l60 :: p59
theorem d60 : IsLinDerivation F p60 :=
  IsLinDerivation.res (C := l22) (D := l8) d59
    (lineAt p59 37 (by decide +kernel)) (lineAt p59 51 (by decide +kernel))
    ⟨({(3,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l61 : LC := {(({(0,0)} : Finset V),true),(({(0,1)} : Finset V),true),(({(1,0)} : Finset V),true),(({(3,0)} : Finset V),true)}
def p61 : List LC := l61 :: p60
theorem d61 : IsLinDerivation F p61 :=
  IsLinDerivation.res (C := l60) (D := l0) d60
    (lineAt p60 0 (by decide +kernel)) (lineAt p60 60 (by decide +kernel))
    ⟨({(1,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l62 : LC := {(({(0,0)} : Finset V),true),(({(1,0)} : Finset V),true),(({(3,0)} : Finset V),true)}
def p62 : List LC := l62 :: p61
theorem d62 : IsLinDerivation F p62 :=
  IsLinDerivation.res (C := l47) (D := l61) d61
    (lineAt p61 14 (by decide +kernel)) (lineAt p61 0 (by decide +kernel))
    ⟨({(0,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l63 : LC := {(({(0,0)} : Finset V),true),(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),true),(({(3,0)} : Finset V),true),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),false)}
def p63 : List LC := l63 :: p62
theorem d63 : IsLinDerivation F p63 :=
  IsLinDerivation.res (C := l45) (D := l62) d62
    (lineAt p62 17 (by decide +kernel)) (lineAt p62 0 (by decide +kernel))
    ⟨({(1,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l64 : LC := {(({(0,0)} : Finset V),true),(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),true),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),false)}
def p64 : List LC := l64 :: p63
theorem d64 : IsLinDerivation F p64 :=
  IsLinDerivation.res (C := l44) (D := l63) d63
    (lineAt p63 19 (by decide +kernel)) (lineAt p63 0 (by decide +kernel))
    ⟨({(3,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l65 : LC := {(({(0,0)} : Finset V),true),(({(2,0)} : Finset V),false),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),false)}
def p65 : List LC := l65 :: p64
theorem d65 : IsLinDerivation F p65 :=
  IsLinDerivation.res (C := l35) (D := l64) d64
    (lineAt p64 29 (by decide +kernel)) (lineAt p64 0 (by decide +kernel))
    ⟨({(2,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l66 : LC := {(({(0,0)} : Finset V),false),(({(0,1)} : Finset V),false),(({(2,0)} : Finset V),false),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),true)}
def p66 : List LC := l66 :: p65
theorem d66 : IsLinDerivation F p66 :=
  IsLinDerivation.res (C := l7) (D := l33) d65
    (lineAt p65 58 (by decide +kernel)) (lineAt p65 32 (by decide +kernel))
    ⟨({(2,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l67 : LC := {(({(0,0)} : Finset V),true),(({(0,1)} : Finset V),false),(({(2,0)} : Finset V),true),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),true)}
def p67 : List LC := l67 :: p66
theorem d67 : IsLinDerivation F p67 :=
  IsLinDerivation.res (C := l6) (D := l32) d66
    (lineAt p66 60 (by decide +kernel)) (lineAt p66 34 (by decide +kernel))
    ⟨({(2,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l68 : LC := {(({(0,0)} : Finset V),true),(({(0,1)} : Finset V),false),(({(1,0)} : Finset V),false),(({(3,0)} : Finset V),false),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),true)}
def p68 : List LC := l68 :: p67
theorem d68 : IsLinDerivation F p68 :=
  IsLinDerivation.res (C := l59) (D := l67) d67
    (lineAt p67 8 (by decide +kernel)) (lineAt p67 0 (by decide +kernel))
    ⟨({(2,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l69 : LC := {(({(0,0)} : Finset V),true),(({(0,1)} : Finset V),false),(({(1,0)} : Finset V),true),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),true)}
def p69 : List LC := l69 :: p68
theorem d69 : IsLinDerivation F p69 :=
  IsLinDerivation.res (C := l2) (D := l24) d68
    (lineAt p68 66 (by decide +kernel)) (lineAt p68 44 (by decide +kernel))
    ⟨({(1,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l70 : LC := {(({(0,0)} : Finset V),true),(({(0,1)} : Finset V),false),(({(3,0)} : Finset V),false),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),true)}
def p70 : List LC := l70 :: p69
theorem d70 : IsLinDerivation F p70 :=
  IsLinDerivation.res (C := l68) (D := l69) d69
    (lineAt p69 1 (by decide +kernel)) (lineAt p69 0 (by decide +kernel))
    ⟨({(1,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l71 : LC := {(({(0,0)} : Finset V),true),(({(3,0)} : Finset V),false),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),true)}
def p71 : List LC := l71 :: p70
theorem d71 : IsLinDerivation F p71 :=
  IsLinDerivation.res (C := l70) (D := l12) d70
    (lineAt p70 0 (by decide +kernel)) (lineAt p70 58 (by decide +kernel))
    ⟨({(0,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l72 : LC := {(({(1,0)} : Finset V),true),(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),true),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),false)}
def p72 : List LC := l72 :: p71
theorem d72 : IsLinDerivation F p72 :=
  IsLinDerivation.res (C := l26) (D := l16) d71
    (lineAt p71 45 (by decide +kernel)) (lineAt p71 55 (by decide +kernel))
    ⟨({(1,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l73 : LC := {(({(1,0)} : Finset V),true),(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),true),(({(4,0)} : Finset V),true)}
def p73 : List LC := l73 :: p72
theorem d73 : IsLinDerivation F p73 :=
  IsLinDerivation.res (C := l72) (D := l32) d72
    (lineAt p72 0 (by decide +kernel)) (lineAt p72 40 (by decide +kernel))
    ⟨({(4,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l74 : LC := {(({(0,0)} : Finset V),false),(({(0,1)} : Finset V),false),(({(1,0)} : Finset V),false),(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),true)}
def p74 : List LC := l74 :: p73
theorem d74 : IsLinDerivation F p74 :=
  IsLinDerivation.res (C := l3) (D := l17) d73
    (lineAt p73 70 (by decide +kernel)) (lineAt p73 56 (by decide +kernel))
    ⟨({(1,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l75 : LC := {(({(0,0)} : Finset V),false),(({(1,0)} : Finset V),false),(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),true)}
def p75 : List LC := l75 :: p74
theorem d75 : IsLinDerivation F p75 :=
  IsLinDerivation.res (C := l74) (D := l5) d74
    (lineAt p74 0 (by decide +kernel)) (lineAt p74 69 (by decide +kernel))
    ⟨({(0,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l76 : LC := {(({(0,0)} : Finset V),false),(({(0,1)} : Finset V),true),(({(1,0)} : Finset V),false),(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),false)}
def p76 : List LC := l76 :: p75
theorem d76 : IsLinDerivation F p76 :=
  IsLinDerivation.res (C := l19) (D := l1) d75
    (lineAt p75 56 (by decide +kernel)) (lineAt p75 74 (by decide +kernel))
    ⟨({(1,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l77 : LC := {(({(0,0)} : Finset V),false),(({(1,0)} : Finset V),false),(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),false)}
def p77 : List LC := l77 :: p76
theorem d77 : IsLinDerivation F p77 :=
  IsLinDerivation.res (C := l7) (D := l76) d76
    (lineAt p76 69 (by decide +kernel)) (lineAt p76 0 (by decide +kernel))
    ⟨({(0,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l78 : LC := {(({(0,0)} : Finset V),false),(({(1,0)} : Finset V),false),(({(2,0)} : Finset V),false)}
def p78 : List LC := l78 :: p77
theorem d78 : IsLinDerivation F p78 :=
  IsLinDerivation.res (C := l77) (D := l75) d77
    (lineAt p77 0 (by decide +kernel)) (lineAt p77 2 (by decide +kernel))
    ⟨({(2,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l79 : LC := {(({(1,0)} : Finset V),true),(({(3,0)} : Finset V),true),(({(3,1)} : Finset V),false),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),true)}
def p79 : List LC := l79 :: p78
theorem d79 : IsLinDerivation F p79 :=
  IsLinDerivation.res (C := l22) (D := l24) d78
    (lineAt p78 56 (by decide +kernel)) (lineAt p78 54 (by decide +kernel))
    ⟨({(1,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l80 : LC := {(({(0,0)} : Finset V),false),(({(0,1)} : Finset V),true),(({(1,0)} : Finset V),false),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),false)}
def p80 : List LC := l80 :: p79
theorem d80 : IsLinDerivation F p80 :=
  IsLinDerivation.res (C := l27) (D := l1) d79
    (lineAt p79 52 (by decide +kernel)) (lineAt p79 78 (by decide +kernel))
    ⟨({(1,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l81 : LC := {(({(0,0)} : Finset V),false),(({(0,1)} : Finset V),true),(({(2,0)} : Finset V),false),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),false)}
def p81 : List LC := l81 :: p80
theorem d81 : IsLinDerivation F p81 :=
  IsLinDerivation.res (C := l35) (D := l5) d80
    (lineAt p80 45 (by decide +kernel)) (lineAt p80 75 (by decide +kernel))
    ⟨({(2,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l82 : LC := {(({(0,0)} : Finset V),false),(({(0,1)} : Finset V),true),(({(3,0)} : Finset V),false),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),false)}
def p82 : List LC := l82 :: p81
theorem d82 : IsLinDerivation F p82 :=
  IsLinDerivation.res (C := l39) (D := l9) d81
    (lineAt p81 42 (by decide +kernel)) (lineAt p81 72 (by decide +kernel))
    ⟨({(3,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l83 : LC := {(({(2,0)} : Finset V),true),(({(3,0)} : Finset V),true),(({(3,1)} : Finset V),true),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),false)}
def p83 : List LC := l83 :: p82
theorem d83 : IsLinDerivation F p83 :=
  IsLinDerivation.res (C := l34) (D := l28) d82
    (lineAt p82 48 (by decide +kernel)) (lineAt p82 54 (by decide +kernel))
    ⟨({(2,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l84 : LC := {(({(0,0)} : Finset V),true),(({(3,0)} : Finset V),true),(({(3,1)} : Finset V),true),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),false)}
def p84 : List LC := l84 :: p83
theorem d84 : IsLinDerivation F p84 :=
  IsLinDerivation.res (C := l14) (D := l8) d83
    (lineAt p83 69 (by decide +kernel)) (lineAt p83 75 (by decide +kernel))
    ⟨({(0,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l85 : LC := {(({(1,0)} : Finset V),false),(({(2,0)} : Finset V),false),(({(3,0)} : Finset V),true),(({(3,1)} : Finset V),true),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),false)}
def p85 : List LC := l85 :: p84
theorem d85 : IsLinDerivation F p85 :=
  IsLinDerivation.res (C := l78) (D := l84) d84
    (lineAt p84 6 (by decide +kernel)) (lineAt p84 0 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l86 : LC := {(({(1,0)} : Finset V),false),(({(3,0)} : Finset V),true),(({(3,1)} : Finset V),true),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),false)}
def p86 : List LC := l86 :: p85
theorem d86 : IsLinDerivation F p86 :=
  IsLinDerivation.res (C := l85) (D := l83) d85
    (lineAt p85 0 (by decide +kernel)) (lineAt p85 2 (by decide +kernel))
    ⟨({(2,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l87 : LC := {(({(1,0)} : Finset V),true),(({(3,0)} : Finset V),true),(({(3,1)} : Finset V),true),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),false)}
def p87 : List LC := l87 :: p86
theorem d87 : IsLinDerivation F p87 :=
  IsLinDerivation.res (C := l26) (D := l20) d86
    (lineAt p86 60 (by decide +kernel)) (lineAt p86 66 (by decide +kernel))
    ⟨({(1,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l88 : LC := {(({(3,0)} : Finset V),true),(({(3,1)} : Finset V),true),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),false)}
def p88 : List LC := l88 :: p87
theorem d88 : IsLinDerivation F p88 :=
  IsLinDerivation.res (C := l86) (D := l87) d87
    (lineAt p87 1 (by decide +kernel)) (lineAt p87 0 (by decide +kernel))
    ⟨({(1,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l89 : LC := {(({(3,0)} : Finset V),true),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),false)}
def p89 : List LC := l89 :: p88
theorem d89 : IsLinDerivation F p89 :=
  IsLinDerivation.res (C := l38) (D := l88) d88
    (lineAt p88 50 (by decide +kernel)) (lineAt p88 0 (by decide +kernel))
    ⟨({(3,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l90 : LC := {(({(1,0)} : Finset V),true),(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),false),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),true)}
def p90 : List LC := l90 :: p89
theorem d90 : IsLinDerivation F p90 :=
  IsLinDerivation.res (C := l18) (D := l24) d89
    (lineAt p89 71 (by decide +kernel)) (lineAt p89 65 (by decide +kernel))
    ⟨({(1,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l91 : LC := {(({(1,0)} : Finset V),true),(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),false),(({(4,0)} : Finset V),true)}
def p91 : List LC := l91 :: p90
theorem d91 : IsLinDerivation F p91 :=
  IsLinDerivation.res (C := l34) (D := l90) d90
    (lineAt p90 56 (by decide +kernel)) (lineAt p90 0 (by decide +kernel))
    ⟨({(4,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l92 : LC := {(({(0,0)} : Finset V),true),(({(0,1)} : Finset V),true),(({(2,0)} : Finset V),true),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),false)}
def p92 : List LC := l92 :: p91
theorem d92 : IsLinDerivation F p92 :=
  IsLinDerivation.res (C := l34) (D := l4) d91
    (lineAt p91 57 (by decide +kernel)) (lineAt p91 87 (by decide +kernel))
    ⟨({(2,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l93 : LC := {(({(0,0)} : Finset V),true),(({(0,1)} : Finset V),true),(({(1,0)} : Finset V),false),(({(3,0)} : Finset V),false),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),false)}
def p93 : List LC := l93 :: p92
theorem d93 : IsLinDerivation F p93 :=
  IsLinDerivation.res (C := l59) (D := l92) d92
    (lineAt p92 33 (by decide +kernel)) (lineAt p92 0 (by decide +kernel))
    ⟨({(2,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l94 : LC := {(({(0,0)} : Finset V),true),(({(0,1)} : Finset V),true),(({(1,0)} : Finset V),true),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),false)}
def p94 : List LC := l94 :: p93
theorem d94 : IsLinDerivation F p94 :=
  IsLinDerivation.res (C := l26) (D := l0) d93
    (lineAt p93 67 (by decide +kernel)) (lineAt p93 93 (by decide +kernel))
    ⟨({(1,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l95 : LC := {(({(0,0)} : Finset V),true),(({(0,1)} : Finset V),true),(({(3,0)} : Finset V),false),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),false)}
def p95 : List LC := l95 :: p94
theorem d95 : IsLinDerivation F p95 :=
  IsLinDerivation.res (C := l93) (D := l94) d94
    (lineAt p94 1 (by decide +kernel)) (lineAt p94 0 (by decide +kernel))
    ⟨({(1,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l96 : LC := {(({(0,0)} : Finset V),true),(({(3,0)} : Finset V),false),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),false)}
def p96 : List LC := l96 :: p95
theorem d96 : IsLinDerivation F p96 :=
  IsLinDerivation.res (C := l14) (D := l95) d95
    (lineAt p95 81 (by decide +kernel)) (lineAt p95 0 (by decide +kernel))
    ⟨({(0,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l97 : LC := {(({(0,0)} : Finset V),true),(({(3,0)} : Finset V),false),(({(4,0)} : Finset V),true)}
def p97 : List LC := l97 :: p96
theorem d97 : IsLinDerivation F p97 :=
  IsLinDerivation.res (C := l96) (D := l71) d96
    (lineAt p96 0 (by decide +kernel)) (lineAt p96 25 (by decide +kernel))
    ⟨({(4,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l98 : LC := {(({(1,0)} : Finset V),true),(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),true),(({(3,0)} : Finset V),true),(({(3,1)} : Finset V),false)}
def p98 : List LC := l98 :: p97
theorem d98 : IsLinDerivation F p98 :=
  IsLinDerivation.res (C := l22) (D := l16) d97
    (lineAt p97 75 (by decide +kernel)) (lineAt p97 81 (by decide +kernel))
    ⟨({(1,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l99 : LC := {(({(1,0)} : Finset V),true),(({(2,0)} : Finset V),true),(({(3,0)} : Finset V),true),(({(3,1)} : Finset V),false)}
def p99 : List LC := l99 :: p98
theorem d99 : IsLinDerivation F p99 :=
  IsLinDerivation.res (C := l30) (D := l98) d98
    (lineAt p98 68 (by decide +kernel)) (lineAt p98 0 (by decide +kernel))
    ⟨({(2,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l100 : LC := {(({(1,0)} : Finset V),true),(({(2,0)} : Finset V),true),(({(3,0)} : Finset V),true)}
def p100 : List LC := l100 :: p99
theorem d100 : IsLinDerivation F p100 :=
  IsLinDerivation.res (C := l99) (D := l49) d99
    (lineAt p99 0 (by decide +kernel)) (lineAt p99 50 (by decide +kernel))
    ⟨({(3,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l101 : LC := {(({(0,0)} : Finset V),false),(({(0,1)} : Finset V),false),(({(1,0)} : Finset V),true),(({(3,0)} : Finset V),true),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),true)}
def p101 : List LC := l101 :: p100
theorem d101 : IsLinDerivation F p101 :=
  IsLinDerivation.res (C := l66) (D := l100) d100
    (lineAt p100 34 (by decide +kernel)) (lineAt p100 0 (by decide +kernel))
    ⟨({(2,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l102 : LC := {(({(0,0)} : Finset V),false),(({(0,1)} : Finset V),true),(({(1,0)} : Finset V),true),(({(2,0)} : Finset V),true),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),false)}
def p102 : List LC := l102 :: p101
theorem d102 : IsLinDerivation F p102 :=
  IsLinDerivation.res (C := l82) (D := l100) d101
    (lineAt p101 19 (by decide +kernel)) (lineAt p101 1 (by decide +kernel))
    ⟨({(3,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l103 : LC := {(({(0,0)} : Finset V),false),(({(0,1)} : Finset V),true),(({(1,0)} : Finset V),true),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),false)}
def p103 : List LC := l103 :: p102
theorem d103 : IsLinDerivation F p103 :=
  IsLinDerivation.res (C := l81) (D := l102) d102
    (lineAt p102 21 (by decide +kernel)) (lineAt p102 0 (by decide +kernel))
    ⟨({(2,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l104 : LC := {(({(0,0)} : Finset V),false),(({(0,1)} : Finset V),true),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),false)}
def p104 : List LC := l104 :: p103
theorem d104 : IsLinDerivation F p104 :=
  IsLinDerivation.res (C := l80) (D := l103) d103
    (lineAt p103 23 (by decide +kernel)) (lineAt p103 0 (by decide +kernel))
    ⟨({(1,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l105 : LC := {(({(0,0)} : Finset V),false),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),false)}
def p105 : List LC := l105 :: p104
theorem d105 : IsLinDerivation F p105 :=
  IsLinDerivation.res (C := l15) (D := l104) d104
    (lineAt p104 89 (by decide +kernel)) (lineAt p104 0 (by decide +kernel))
    ⟨({(0,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l106 : LC := {(({(0,0)} : Finset V),false),(({(0,1)} : Finset V),false),(({(2,0)} : Finset V),false),(({(3,0)} : Finset V),false),(({(3,1)} : Finset V),true)}
def p106 : List LC := l106 :: p105
theorem d106 : IsLinDerivation F p106 :=
  IsLinDerivation.res (C := l7) (D := l29) d105
    (lineAt p105 98 (by decide +kernel)) (lineAt p105 76 (by decide +kernel))
    ⟨({(2,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l107 : LC := {(({(1,0)} : Finset V),true),(({(2,0)} : Finset V),true),(({(4,0)} : Finset V),true)}
def p107 : List LC := l107 :: p106
theorem d107 : IsLinDerivation F p107 :=
  IsLinDerivation.res (C := l91) (D := l73) d106
    (lineAt p106 15 (by decide +kernel)) (lineAt p106 33 (by decide +kernel))
    ⟨({(2,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l108 : LC := {(({(0,0)} : Finset V),false),(({(0,1)} : Finset V),false),(({(1,0)} : Finset V),true),(({(3,0)} : Finset V),false),(({(3,1)} : Finset V),true),(({(4,0)} : Finset V),true)}
def p108 : List LC := l108 :: p107
theorem d108 : IsLinDerivation F p108 :=
  IsLinDerivation.res (C := l106) (D := l107) d107
    (lineAt p107 1 (by decide +kernel)) (lineAt p107 0 (by decide +kernel))
    ⟨({(2,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l109 : LC := {(({(0,0)} : Finset V),false),(({(0,1)} : Finset V),false),(({(1,0)} : Finset V),false),(({(3,0)} : Finset V),false),(({(3,1)} : Finset V),true)}
def p109 : List LC := l109 :: p108
theorem d109 : IsLinDerivation F p109 :=
  IsLinDerivation.res (C := l3) (D := l21) d108
    (lineAt p108 105 (by decide +kernel)) (lineAt p108 87 (by decide +kernel))
    ⟨({(1,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l110 : LC := {(({(0,0)} : Finset V),false),(({(0,1)} : Finset V),false),(({(3,0)} : Finset V),false),(({(3,1)} : Finset V),true),(({(4,0)} : Finset V),true)}
def p110 : List LC := l110 :: p109
theorem d110 : IsLinDerivation F p110 :=
  IsLinDerivation.res (C := l109) (D := l108) d109
    (lineAt p109 0 (by decide +kernel)) (lineAt p109 1 (by decide +kernel))
    ⟨({(1,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l111 : LC := {(({(0,0)} : Finset V),false),(({(0,1)} : Finset V),false),(({(3,0)} : Finset V),false),(({(4,0)} : Finset V),true)}
def p111 : List LC := l111 :: p110
theorem d111 : IsLinDerivation F p111 :=
  IsLinDerivation.res (C := l11) (D := l110) d110
    (lineAt p110 99 (by decide +kernel)) (lineAt p110 0 (by decide +kernel))
    ⟨({(3,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l112 : LC := {(({(0,0)} : Finset V),true),(({(0,1)} : Finset V),false),(({(1,0)} : Finset V),true),(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),true)}
def p112 : List LC := l112 :: p111
theorem d112 : IsLinDerivation F p112 :=
  IsLinDerivation.res (C := l2) (D := l16) d111
    (lineAt p111 109 (by decide +kernel)) (lineAt p111 95 (by decide +kernel))
    ⟨({(1,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l113 : LC := {(({(0,0)} : Finset V),true),(({(0,1)} : Finset V),false),(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),true),(({(3,0)} : Finset V),false),(({(4,0)} : Finset V),false)}
def p113 : List LC := l113 :: p112
theorem d113 : IsLinDerivation F p113 :=
  IsLinDerivation.res (C := l55) (D := l112) d112
    (lineAt p112 57 (by decide +kernel)) (lineAt p112 0 (by decide +kernel))
    ⟨({(1,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l114 : LC := {(({(0,0)} : Finset V),true),(({(0,1)} : Finset V),false),(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),true),(({(3,0)} : Finset V),true)}
def p114 : List LC := l114 :: p113
theorem d114 : IsLinDerivation F p114 :=
  IsLinDerivation.res (C := l10) (D := l28) d113
    (lineAt p113 103 (by decide +kernel)) (lineAt p113 85 (by decide +kernel))
    ⟨({(3,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l115 : LC := {(({(0,0)} : Finset V),true),(({(0,1)} : Finset V),false),(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),true),(({(4,0)} : Finset V),false)}
def p115 : List LC := l115 :: p114
theorem d115 : IsLinDerivation F p115 :=
  IsLinDerivation.res (C := l113) (D := l114) d114
    (lineAt p114 1 (by decide +kernel)) (lineAt p114 0 (by decide +kernel))
    ⟨({(3,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l116 : LC := {(({(0,0)} : Finset V),true),(({(0,1)} : Finset V),false),(({(2,0)} : Finset V),true),(({(4,0)} : Finset V),false)}
def p116 : List LC := l116 :: p115
theorem d116 : IsLinDerivation F p116 :=
  IsLinDerivation.res (C := l6) (D := l115) d115
    (lineAt p115 109 (by decide +kernel)) (lineAt p115 0 (by decide +kernel))
    ⟨({(2,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l117 : LC := {(({(0,0)} : Finset V),true),(({(3,0)} : Finset V),true),(({(3,1)} : Finset V),false),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),true)}
def p117 : List LC := l117 :: p116
theorem d117 : IsLinDerivation F p117 :=
  IsLinDerivation.res (C := l10) (D := l12) d116
    (lineAt p116 106 (by decide +kernel)) (lineAt p116 104 (by decide +kernel))
    ⟨({(0,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l118 : LC := {(({(1,0)} : Finset V),false),(({(2,0)} : Finset V),false),(({(3,0)} : Finset V),true),(({(3,1)} : Finset V),false),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),true)}
def p118 : List LC := l118 :: p117
theorem d118 : IsLinDerivation F p118 :=
  IsLinDerivation.res (C := l78) (D := l117) d117
    (lineAt p117 39 (by decide +kernel)) (lineAt p117 0 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l119 : LC := {(({(1,0)} : Finset V),false),(({(3,0)} : Finset V),true),(({(3,1)} : Finset V),false),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),true)}
def p119 : List LC := l119 :: p118
theorem d119 : IsLinDerivation F p119 :=
  IsLinDerivation.res (C := l118) (D := l52) d118
    (lineAt p118 0 (by decide +kernel)) (lineAt p118 66 (by decide +kernel))
    ⟨({(2,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l120 : LC := {(({(3,0)} : Finset V),true),(({(3,1)} : Finset V),false),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),true)}
def p120 : List LC := l120 :: p119
theorem d120 : IsLinDerivation F p120 :=
  IsLinDerivation.res (C := l119) (D := l79) d119
    (lineAt p119 0 (by decide +kernel)) (lineAt p119 40 (by decide +kernel))
    ⟨({(1,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l121 : LC := {(({(3,0)} : Finset V),true),(({(4,0)} : Finset V),true),(({(4,1)} : Finset V),true)}
def p121 : List LC := l121 :: p120
theorem d121 : IsLinDerivation F p121 :=
  IsLinDerivation.res (C := l120) (D := l36) d120
    (lineAt p120 0 (by decide +kernel)) (lineAt p120 84 (by decide +kernel))
    ⟨({(3,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l122 : LC := {(({(3,0)} : Finset V),true),(({(4,0)} : Finset V),true)}
def p122 : List LC := l122 :: p121
theorem d122 : IsLinDerivation F p122 :=
  IsLinDerivation.res (C := l89) (D := l121) d121
    (lineAt p121 32 (by decide +kernel)) (lineAt p121 0 (by decide +kernel))
    ⟨({(4,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l123 : LC := {(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),false),(({(3,0)} : Finset V),false),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),true)}
def p123 : List LC := l123 :: p122
theorem d123 : IsLinDerivation F p123 :=
  IsLinDerivation.res (C := l31) (D := l37) d122
    (lineAt p122 91 (by decide +kernel)) (lineAt p122 85 (by decide +kernel))
    ⟨({(3,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l124 : LC := {(({(0,0)} : Finset V),true),(({(1,0)} : Finset V),true),(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),false),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),true)}
def p124 : List LC := l124 :: p123
theorem d124 : IsLinDerivation F p124 :=
  IsLinDerivation.res (C := l123) (D := l62) d123
    (lineAt p123 0 (by decide +kernel)) (lineAt p123 61 (by decide +kernel))
    ⟨({(3,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l125 : LC := {(({(0,0)} : Finset V),true),(({(2,0)} : Finset V),false),(({(2,1)} : Finset V),false),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),true)}
def p125 : List LC := l125 :: p124
theorem d125 : IsLinDerivation F p125 :=
  IsLinDerivation.res (C := l56) (D := l124) d124
    (lineAt p124 68 (by decide +kernel)) (lineAt p124 0 (by decide +kernel))
    ⟨({(1,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l126 : LC := {(({(0,0)} : Finset V),true),(({(2,0)} : Finset V),false),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),true)}
def p126 : List LC := l126 :: p125
theorem d126 : IsLinDerivation F p126 :=
  IsLinDerivation.res (C := l125) (D := l33) d125
    (lineAt p125 0 (by decide +kernel)) (lineAt p125 92 (by decide +kernel))
    ⟨({(2,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l127 : LC := {(({(0,0)} : Finset V),true),(({(2,0)} : Finset V),false),(({(4,0)} : Finset V),false)}
def p127 : List LC := l127 :: p126
theorem d127 : IsLinDerivation F p127 :=
  IsLinDerivation.res (C := l65) (D := l126) d126
    (lineAt p126 61 (by decide +kernel)) (lineAt p126 0 (by decide +kernel))
    ⟨({(4,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l128 : LC := {(({(0,0)} : Finset V),true),(({(0,1)} : Finset V),true),(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),false),(({(3,0)} : Finset V),true)}
def p128 : List LC := l128 :: p127
theorem d128 : IsLinDerivation F p128 :=
  IsLinDerivation.res (C := l30) (D := l8) d127
    (lineAt p127 97 (by decide +kernel)) (lineAt p127 119 (by decide +kernel))
    ⟨({(3,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l129 : LC := {(({(0,0)} : Finset V),true),(({(0,1)} : Finset V),true),(({(1,0)} : Finset V),false),(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),false),(({(4,0)} : Finset V),false)}
def p129 : List LC := l129 :: p128
theorem d129 : IsLinDerivation F p129 :=
  IsLinDerivation.res (C := l55) (D := l128) d128
    (lineAt p128 73 (by decide +kernel)) (lineAt p128 0 (by decide +kernel))
    ⟨({(3,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l130 : LC := {(({(0,0)} : Finset V),true),(({(0,1)} : Finset V),true),(({(2,0)} : Finset V),true),(({(2,1)} : Finset V),false),(({(4,0)} : Finset V),false)}
def p130 : List LC := l130 :: p129
theorem d130 : IsLinDerivation F p130 :=
  IsLinDerivation.res (C := l129) (D := l43) d129
    (lineAt p129 0 (by decide +kernel)) (lineAt p129 86 (by decide +kernel))
    ⟨({(1,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l131 : LC := {(({(0,0)} : Finset V),true),(({(0,1)} : Finset V),true),(({(2,0)} : Finset V),true),(({(4,0)} : Finset V),false)}
def p131 : List LC := l131 :: p130
theorem d131 : IsLinDerivation F p131 :=
  IsLinDerivation.res (C := l130) (D := l4) d130
    (lineAt p130 0 (by decide +kernel)) (lineAt p130 126 (by decide +kernel))
    ⟨({(2,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l132 : LC := {(({(0,0)} : Finset V),true),(({(2,0)} : Finset V),true),(({(4,0)} : Finset V),false)}
def p132 : List LC := l132 :: p131
theorem d132 : IsLinDerivation F p132 :=
  IsLinDerivation.res (C := l116) (D := l131) d131
    (lineAt p131 15 (by decide +kernel)) (lineAt p131 0 (by decide +kernel))
    ⟨({(0,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l133 : LC := {(({(0,0)} : Finset V),true),(({(4,0)} : Finset V),false)}
def p133 : List LC := l133 :: p132
theorem d133 : IsLinDerivation F p133 :=
  IsLinDerivation.res (C := l127) (D := l132) d132
    (lineAt p132 5 (by decide +kernel)) (lineAt p132 0 (by decide +kernel))
    ⟨({(2,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l134 : LC := {(({(0,0)} : Finset V),false),(({(0,1)} : Finset V),false),(({(1,0)} : Finset V),false),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),true)}
def p134 : List LC := l134 :: p133
theorem d134 : IsLinDerivation F p134 :=
  IsLinDerivation.res (C := l3) (D := l25) d133
    (lineAt p133 130 (by decide +kernel)) (lineAt p133 108 (by decide +kernel))
    ⟨({(1,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l135 : LC := {(({(0,0)} : Finset V),false),(({(0,1)} : Finset V),false),(({(3,0)} : Finset V),true),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),true)}
def p135 : List LC := l135 :: p134
theorem d135 : IsLinDerivation F p135 :=
  IsLinDerivation.res (C := l134) (D := l101) d134
    (lineAt p134 0 (by decide +kernel)) (lineAt p134 33 (by decide +kernel))
    ⟨({(1,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l136 : LC := {(({(0,0)} : Finset V),false),(({(0,1)} : Finset V),false),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),true)}
def p136 : List LC := l136 :: p135
theorem d136 : IsLinDerivation F p136 :=
  IsLinDerivation.res (C := l42) (D := l135) d135
    (lineAt p135 93 (by decide +kernel)) (lineAt p135 0 (by decide +kernel))
    ⟨({(3,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l137 : LC := {(({(0,0)} : Finset V),false),(({(4,0)} : Finset V),false),(({(4,1)} : Finset V),true)}
def p137 : List LC := l137 :: p136
theorem d137 : IsLinDerivation F p137 :=
  IsLinDerivation.res (C := l136) (D := l13) d136
    (lineAt p136 0 (by decide +kernel)) (lineAt p136 123 (by decide +kernel))
    ⟨({(0,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l138 : LC := {(({(0,0)} : Finset V),false),(({(4,0)} : Finset V),false)}
def p138 : List LC := l138 :: p137
theorem d138 : IsLinDerivation F p138 :=
  IsLinDerivation.res (C := l105) (D := l137) d137
    (lineAt p137 32 (by decide +kernel)) (lineAt p137 0 (by decide +kernel))
    ⟨({(4,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l139 : LC := {(({(4,0)} : Finset V),false)}
def p139 : List LC := l139 :: p138
theorem d139 : IsLinDerivation F p139 :=
  IsLinDerivation.res (C := l138) (D := l133) d138
    (lineAt p138 0 (by decide +kernel)) (lineAt p138 5 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l140 : LC := {(({(0,0)} : Finset V),false),(({(0,1)} : Finset V),true),(({(1,0)} : Finset V),false),(({(3,0)} : Finset V),false),(({(3,1)} : Finset V),false)}
def p140 : List LC := l140 :: p139
theorem d140 : IsLinDerivation F p140 :=
  IsLinDerivation.res (C := l23) (D := l1) d139
    (lineAt p139 116 (by decide +kernel)) (lineAt p139 138 (by decide +kernel))
    ⟨({(1,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l141 : LC := {(({(0,0)} : Finset V),false),(({(0,1)} : Finset V),true),(({(2,0)} : Finset V),true),(({(3,0)} : Finset V),false),(({(3,1)} : Finset V),false),(({(4,0)} : Finset V),true)}
def p141 : List LC := l141 :: p140
theorem d141 : IsLinDerivation F p141 :=
  IsLinDerivation.res (C := l140) (D := l107) d140
    (lineAt p140 0 (by decide +kernel)) (lineAt p140 33 (by decide +kernel))
    ⟨({(1,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l142 : LC := {(({(0,0)} : Finset V),false),(({(0,1)} : Finset V),true),(({(2,0)} : Finset V),false),(({(3,0)} : Finset V),false),(({(3,1)} : Finset V),false)}
def p142 : List LC := l142 :: p141
theorem d142 : IsLinDerivation F p142 :=
  IsLinDerivation.res (C := l31) (D := l5) d141
    (lineAt p141 110 (by decide +kernel)) (lineAt p141 136 (by decide +kernel))
    ⟨({(2,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l143 : LC := {(({(0,0)} : Finset V),false),(({(0,1)} : Finset V),true),(({(3,0)} : Finset V),false),(({(3,1)} : Finset V),false),(({(4,0)} : Finset V),true)}
def p143 : List LC := l143 :: p142
theorem d143 : IsLinDerivation F p143 :=
  IsLinDerivation.res (C := l142) (D := l141) d142
    (lineAt p142 0 (by decide +kernel)) (lineAt p142 1 (by decide +kernel))
    ⟨({(2,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l144 : LC := {(({(0,0)} : Finset V),false),(({(0,1)} : Finset V),true),(({(3,0)} : Finset V),false),(({(4,0)} : Finset V),true)}
def p144 : List LC := l144 :: p143
theorem d144 : IsLinDerivation F p144 :=
  IsLinDerivation.res (C := l143) (D := l9) d143
    (lineAt p143 0 (by decide +kernel)) (lineAt p143 134 (by decide +kernel))
    ⟨({(3,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l145 : LC := {(({(0,0)} : Finset V),false),(({(3,0)} : Finset V),false),(({(4,0)} : Finset V),true)}
def p145 : List LC := l145 :: p144
theorem d145 : IsLinDerivation F p145 :=
  IsLinDerivation.res (C := l111) (D := l144) d144
    (lineAt p144 33 (by decide +kernel)) (lineAt p144 0 (by decide +kernel))
    ⟨({(0,1)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l146 : LC := {(({(3,0)} : Finset V),false),(({(4,0)} : Finset V),true)}
def p146 : List LC := l146 :: p145
theorem d146 : IsLinDerivation F p146 :=
  IsLinDerivation.res (C := l145) (D := l97) d145
    (lineAt p145 0 (by decide +kernel)) (lineAt p145 48 (by decide +kernel))
    ⟨({(0,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l147 : LC := {(({(4,0)} : Finset V),true)}
def p147 : List LC := l147 :: p146
theorem d147 : IsLinDerivation F p147 :=
  IsLinDerivation.res (C := l146) (D := l122) d146
    (lineAt p146 0 (by decide +kernel)) (lineAt p146 24 (by decide +kernel))
    ⟨({(3,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

def l148 : LC := ∅
def p148 : List LC := l148 :: p147
theorem d148 : IsLinDerivation F p148 :=
  IsLinDerivation.res (C := l139) (D := l147) d147
    (lineAt p147 8 (by decide +kernel)) (lineAt p147 0 (by decide +kernel))
    ⟨({(4,0)} : Finset V), by decide +kernel, by decide +kernel, by decide +kernel⟩

end BinaryFiveCertificate

open BinaryFiveCertificate in
theorem BinaryFiveCertificate.refutation : ∃ π : List (PEqualNP.ProofComplexity.LinClause (Fin 5 × Fin 2)), PEqualNP.ProofComplexity.IsLinRefutation (PEqualNP.ProofComplexity.BPHP 5 2) π ∧ π.length ≤ 149 :=
  ⟨p148, ⟨d148, List.Mem.head _⟩, by decide +kernel⟩
