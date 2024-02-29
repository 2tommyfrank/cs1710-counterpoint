# Modeling Cantus Firmi in Froglet

### Project Objective

In addition to melody, rhythm, and harmony, one other important element of music is counterpoint. Counterpoint is the juxtaposition of multiple musical lines which sound distinct yet harmonious. It's usually taught using a *cantus firmus* (plural: cantus firmi) line, which is like a main melody, and another *counterpoint* line that complements the cantus firmus and belongs to one of four different *species*. In this project, we model cantus firmi, which are required to follow a set of restrictive rules. We sought to understand which of these rules are important to aesthetic quality. The cantus firmi rules are already complex to model, so we decided not to model counterpoint. However, modeling first species counterpoint could be a good way to extend this project.

https://en.wikipedia.org/wiki/Counterpoint

### Model Design

We chose to use only one sig for cantus firmi as opposed to having sigs to represent individual notes in order to reduce modeling complexity. We represented notes as pitches relative to the starting note rather than absolute pitches in order to simplify some logic relating to intervals, but at the cost of a slightly more complicated `noTritones` predicate. To make our predicates more scalable to other use cases with a larger allowed range of notes, we compared pitches mod 7 to determine tritones. Lastly, in order to make use of built-in sequence helpers (e.g. `isSeqOf` in the `wellformed` predicate), we used an integer bitwidth of 5.

### Visualization

We wrote a custom visualizer inspired by a [former student's musical scales visualizer](https://github.com/csci1710/public-examples/tree/main/muscal_scales)\* but with some significant differences; see `cf_visualizer.js`. The visualizer is automatically included in Sterling; it uses \<svg\> and plays sound! It uses this [whole note image](https://uploads-ssl.webflow.com/5d88ada011bed54810655344/5dd5689265518fb9e5a43148_Whole-note-musical-symbols-classical-music-blog-semibreve-min.png) and this [alto clef image](https://openclipart.org/image/800px/270451) from the web.

\*note to Tim: the name of the repo is misspelled :(

### Signatures and Predicates

We only have one sig, representing a single cantus firmus. Each predicate enforces one of the guidelines from `Cantus firmus guidelines.pdf` (taken from MUSC0550: Theory of Tonal Music I), along with a main `cantusFirmus` predicate that enforces all of them together.

### Running and Testing

We have three run statements at the bottom of `cantus_firmus.frg`; see comments there for details. We tested each predicate and function with overconstraint and underconstraint tests; see `cantus_firmus.tests.frg`. Note that it suffices to check `cantusFirmus` is satisfiable; checking that all the sub-predicates are also satisfiable is redundant. We did not test any profound properties about cantus firmi because this modeling project was more bottom-up (i.e. starting from constraints and finding examples) rather than top-down (i.e. starting from known examples and coming up with constraints). However, we did learn something about the constraints, as explained below.

We also include a `cantusFirmusLite` predicate that encapsulates all but two of the sub-predicates. We originally didn't include these predicates, which prevent the cantus firmus from circling around the same note and prevent it from jumping twice in a row. In the course of testing the model, we found that the lack of these constraints made the cantus firmi less aesthetically pleasing. One could say this modeling project helped us gain an appreciation for constraints like these, which may seem arbitrary but ultimately have a noticeable effect on aesthetic quality.

To see the difference, try running the `cantusFirmusLite` run statement and listening to the generated examples using the visualizer. The difference is definitely subtle but might become more noticeable as you listen to more examples.