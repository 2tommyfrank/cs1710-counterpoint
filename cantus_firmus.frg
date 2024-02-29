#lang forge/bsl

// Cantus firmus
one sig Cf {
    mode: one Int,
    degrees: pfunc Int -> Int
}

// Tommy
fun lastMeasure: Int {
    max[{ i: Int | some Cf.degrees[i] }]
}

// Ethan
fun intervalOf[i, j : Int] : Int {
    add[abs[subtract[j, i]], 1]
}

// Tommy
pred wellformed {
    Cf.mode >= 0
    Cf.mode <= 6
    some Cf.degrees[0]
    isSeqOf[Cf.degrees, Int]
}

// Ethan
pred validMode {
    let F = 3, B = 6 {
        Cf.mode != F
        Cf.mode != B
    }
}

// Ethan
pred validLength {
    lastMeasure >= 7
    lastMeasure <= 15
}

// Ethan
//starts and ends on modal final
pred validStartEnd {
    seqFirst[Cf.degrees] = 0
    seqLast[Cf.degrees] = 0
}

// Ethan
pred validRange {
    all disj i, j: Int {
        intervalOf[Cf.degrees[i], Cf.degrees[j]] <= 8
    }
    some disj i, j: Int {
        intervalOf[Cf.degrees[i], Cf.degrees[j]] >= 5
    }   
}

// Tommy
pred penultimateDescent {
    Cf.degrees[subtract[lastMeasure, 1]] = 1
}

// Ethan
pred validClimax {
    some i: Int | all j: Int | i != j implies {
        Cf.degrees[i] > Cf.degrees[j]
        Cf.degrees[i] != 6 // no seventh climax
        // Cf.degrees[i] > 1
    }
}

// Tommy
fun mod[a, p: Int]: Int {
    let rem = remainder[a, p] {
        rem >= 0 implies rem else add[p, rem]
    }
}

// Tommy
pred tritone[pitch1, pitch2: Int] {
    let F = mod[subtract[3, Cf.mode], 7], B = mod[subtract[6, Cf.mode], 7] {
        (mod[pitch1, 7] = F and mod[pitch2, 7] = B) or
        (mod[pitch1, 7] = B and mod[pitch2, 7] = F)
    }
}

// Tommy
pred noTritones {
    no disj i, j: Int | {
        0 <= i
        i < j
        j <= lastMeasure
        tritone[Cf.degrees[i], Cf.degrees[j]]

        (all m: Int | (i <= m and m < j) implies {
            Cf.degrees[m] < Cf.degrees[add[m, 1]]
        })
        or
        (all m: Int | (i <= m and m < j) implies {
            Cf.degrees[m] > Cf.degrees[add[m, 1]]
        })
    }
}

// Ethan
pred noBadIntervals {
    all i : Int | let j = add[i, 1] {
        (i >= 0 and i < lastMeasure) implies {
            intervalOf[Cf.degrees[i], Cf.degrees[j]] != 1
            intervalOf[Cf.degrees[i], Cf.degrees[j]] != 7
        }
    }
}

// Tommy
pred mostlySteps {
    let numJumps = #{ i: Int | let j = add[i, 1] {
        i >= 0
        i < lastMeasure
        intervalOf[Cf.degrees[i], Cf.degrees[j]] > 2
    }} {
        numJumps < divide[lastMeasure, 2]
        numJumps > 0
    }
}

// Ethan
pred noArpeggios {
    no i: Int | let j = add[i, 1], k = add[i, 2] {
        sign[subtract[Cf.degrees[i], Cf.degrees[j]]]
        = sign[subtract[Cf.degrees[j], Cf.degrees[k]]]
        intervalOf[Cf.degrees[i], Cf.degrees[j]] > 2
        intervalOf[Cf.degrees[j], Cf.degrees[k]] > 2
    }
}

// Tommy
pred noCircling {
    no i: Int | let j = add[i, 2], k = add[i, 4] {
        i >= 0
        i <= subtract[lastMeasure, 4]
        Cf.degrees[i] = Cf.degrees[j]
        Cf.degrees[j] = Cf.degrees[k]
    }
}

// Ethan
pred noTripleJump { // this is not track and field
    no i: Int | let j = add[i, 1], k = add[i, 2], m = add[i, 3] {
        intervalOf[Cf.degrees[i], Cf.degrees[j]] > 2
        intervalOf[Cf.degrees[j], Cf.degrees[k]] > 2
        intervalOf[Cf.degrees[k], Cf.degrees[m]] > 2
    }
}

pred cantusFirmus {
    wellformed
    validMode
    validLength
    validStartEnd
    validRange
    penultimateDescent
    validClimax
    noTritones
    noBadIntervals
    mostlySteps
    noArpeggios
    noCircling
    noTripleJump
}

run { cantusFirmus } for 5 Int
