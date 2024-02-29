# Modeling Counterpoint in Froglet

### Project Objective

In addition to melody, rhythm, and harmony, one other important element of music is counterpoint. Counterpoint is the juxtaposition of multiple musical lines which sound distinct yet harmonious. It's usually taught using a *cantus firmus* line, which is like a main melody, and another *counterpoint* line that complements the cantus firmus and belongs to one of four different *species*. In this project, we model cantus firmi, which are required to follow a set of restrictive rules. These rules are already complex to model, so we decided not to model counterpoint. However, modeling first species counterpoint could be a good way to extend this project.

https://en.wikipedia.org/wiki/Counterpoint

### Model Design

We chose to use only one sig for cantus firmi as opposed to having sigs to represent individual notes in order to reduce modeling complexity. We represented notes as pitches relative to the starting note rather than absolute pitches in order to simplify some logic relating to intervals, but at the cost of a slightly more complicated `noTritones` predicate. To make our predicates more scalable to other use cases with a larger allowed range of notes, we compared pitches mod 7 to determine tritones. Lastly, in order to make use of built-in sequence helpers (e.g. `isSeqOf` in the `wellformed` predicate), we used an integer bitwidth of 5.

### Visualization

We wrote a custom visualizer inspired by a [former student's musical scales visualizer](https://github.com/csci1710/public-examples/tree/main/muscal_scales)\* but with some significant differences; see `cf_visualizer.js`. The visualizer is automatically included in Sterling; it uses \<svg\> and plays sound! It uses this [whole note image](https://uploads-ssl.webflow.com/5d88ada011bed54810655344/5dd5689265518fb9e5a43148_Whole-note-musical-symbols-classical-music-blog-semibreve-min.png) and this [alto clef image](https://openclipart.org/image/800px/270451).

\*note to Tim: the name of the repo is misspelled :(

### Signatures and Predicates

We only have one sig, representing a single cantus firmus. Each predicate enforces one of the guidelines from `Cantus firmus guidelines.pdf`, along with a main `cantusFirmus` predicate that enforces all of them together.

### Running and Testing

We have three run statements at the bottom of `cantus_firmus.frg`; see comments there for details. We tested each predicate and function with overconstraint and underconstraint tests; see `cantus_firmus.tests.frg`.
