#lang forge/bsl
open "cantus_firmus.frg"

test expect { // lastMeasure
    lastMeasurePresent : {
        some Cf.degrees[15]
        lastMeasure = 15
    } for 5 Int is theorem
    lastMeasureAbsent : {
        no Cf.degrees[15]
        lastMeasure < 15
    } for 5 Int is theorem
}

test expect { // wellformed
    wellformedExample : {
        {   all i: Int | some Cf.degrees[i] iff (i >= 0 and i <= 7)
            Cf.mode = 0
        } implies wellformed
    } for 5 Int is sat
    skippedMeasure : {
        some Cf.degrees[2]
        no Cf.degrees[1]
        wellformed
    } for 5 Int is unsat
    negativeMeasure : {
        some Cf.degrees[-1]
        wellformed
    } for 5 Int is unsat
}

test expect { // penultimateDescent
    penultimateDescentExample : {
        {   Cf.degrees[6] = 1
            Cf.degrees[7] = 0
            no Cf.degrees[8]
            wellformed
        } implies penultimateDescent
    } for 5 Int is sat
    penultimateAscent : {
        Cf.degrees[6] = -1
        Cf.degrees[7] = 0
        no Cf.degrees[8]
        wellformed penultimateDescent
    } for 5 Int is unsat
    antepenultimateDescent : {
        Cf.degrees[5] = 1
        Cf.degrees[6] = 0
        Cf.degrees[7] = 0
        no Cf.degrees[8]
        wellformed penultimateDescent
    } for 5 Int is unsat
}

test expect { // mod
    mod_5_7 : { mod[5, 7] = 5 } for 5 Int is sat
    mod_12_5 : { mod[12, 5] = 2 } for 5 Int is sat
    negative : { mod[-6, 5] = 4 } for 5 Int is sat
}

test expect { // tritone
    ionianTritone : {
        Cf.mode = 0
        tritone[3, 6]
    } for 5 Int is sat
    aeolianTritone : {
        Cf.mode = 5
        tritone[1, -2]
    } for 5 Int is sat
    upperOctaveTritone : {
        Cf.mode = 0
        tritone[10, 13]
    } for 5 Int is sat
    perfectFourth : {
        Cf.mode = 0
        not tritone[2, 5]
    } for 5 Int is sat
    symmetric : {
        all i, j: Int | tritone[i, j] iff tritone[j, i]
    } for 5 Int is theorem
}

test expect { // noTritones
    noTritonesExample : {
        Cf.mode = 0
        Cf.degrees = // C F E B A D C
        0 -> 0 + 1 -> 3 + 2 -> 2 + 3 -> 6 + 4 -> 5 + 5 -> 1 + 6 -> 0
        noTritones
    } for 5 Int is sat
    immediateTritone : {
        Cf.mode = 0
        some i: Int | Cf.degrees[i] = 3 and Cf.degrees[add[i, 1]] = 6
        noTritones
    } for 5 Int is unsat
    tritoneInSequence : {
        Cf.mode = 0
        Cf.degrees[2] = 6 and Cf.degrees[3] = 5 and Cf.degrees[4] = 3
        noTritones
    } for 5 Int is unsat
    noFourthsOrFifths : {
        no i, j: Int | let inter = intervalOf[Cf.degrees[i], Cf.degrees[j]] {
            inter = 4 or inter = 5
        }
        noTritones
    } for 5 Int is theorem
}

test expect { // mostlySteps
    evenMeasureExample : {
        Cf.degrees = // in Ionian: C F E D G A D C
        0 -> 0 + 1 -> 3 + 2 -> 2 + 3 -> 1 + 4 -> 4 + 5 -> 5 + 6 -> 1 + 7 -> 0
        mostlySteps
    } for 5 Int is sat
    oddMeasureExample : {
        Cf.degrees = // in Ionian: C B F E D G A D C
        0 -> 0 + 1 -> -1 + 2 -> 3 + 3 -> 2 + 4 -> 1 + 5 -> 4 + 6 -> 5
        + 7 -> 1 + 8 -> 0
        mostlySteps
    } for 5 Int is sat
    tooManyJumps : {
        Cf.degrees = // in Ionian: C G C G C G D C
        0 -> 0 + 1 -> 4 + 2 -> 0 + 3 -> 4 + 4 -> 0 + 5 -> 4 + 6 -> 1 + 7 -> 0
        mostlySteps
    } for 5 Int is unsat
    noJumps : {
        Cf.degrees = // in Ionian: C D E F G F E D C
        0 -> 0 + 1 -> 1 + 2 -> 2 + 3 -> 3 + 4 -> 4 + 5 -> 3 + 6 -> 2
        + 7 -> 1 + 8 -> 0
        mostlySteps
    } for 5 Int is unsat
}

test expect { // noCircling
    marginalExample : {
        Cf.degrees = // In Ionian: C B C B D C D C
        0 -> 0 + 1 -> -1 + 2 -> 0 + 3 -> -1 + 4 -> 1 + 5 -> 0 + 6 -> 1 + 7 -> 0
        noCircling
    } for 5 Int is sat
    upDownDownUp : {
        Cf.degrees = // In Ionian: C G A G E G D C
        0 -> 0 + 1 -> 4 + 2 -> 5 + 3 -> 4 + 4 -> 2 + 5 -> 4 + 6 -> 1 + 7 -> 0
        noCircling
    } for 5 Int is unsat
    upDownUpDown : {
        Cf.degrees = // In Ionian: C G A G A G D C
        0 -> 0 + 1 -> 4 + 2 -> 5 + 3 -> 4 + 4 -> 5 + 5 -> 4 + 6 -> 1 + 7 -> 0
        noCircling
    } for 5 Int is unsat
}

test expect { // cantusFirmus
    // ensures that all sub-predicates are satisfiable as well
    cfSat : { cantusFirmus } for 5 Int is sat
}
