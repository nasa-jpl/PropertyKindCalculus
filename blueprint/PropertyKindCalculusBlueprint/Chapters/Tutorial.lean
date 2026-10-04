import Verso
import VersoManual
import VersoBlueprint
import PropertyKindCalculusBlueprint.References
import PropertyKindCalculusBlueprint.Chapters.Tutorial.T0_OneNumberTwoKinds
import PropertyKindCalculusBlueprint.Chapters.Tutorial.T1_Objects

-- The tutorial part. Its chapters live in `Chapters/Tutorial/` and are included one level
-- down; they carry no nodes and define no terms, so they add nothing to the status counts.

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Tutorial: a first model, checked" =>
%%%
tag := "tutorial"
%%%

This part is for a reader who will _write_ a model and may never read a proof. The
reference chapters that follow are organized for the other reader — kind first, the
measured object well after — and this part is organized for the first, in the order a model
is actually written, which is the order of Lowe's four-category square read from its
bottom-left corner: the objects measured, the kinds of property measured of them, the
individual quantity that joins the two, the algebra that combines quantities, the sums over
parts, the boundary that says what enters and leaves, and the requirements the model states
against that boundary. Each chapter has one shape: what you write, what the machine
accepts, what it refuses and the error it prints, what a dimension-and-units library would
have done with the same line, and one pointer to the reference chapter that proves the step.

The running example is a harmonic oscillator, two bodies coupled by three springs — the
system `ForPhysLib.CaseStudies.HarmonicOscillator` types four ways and scores against
ForPhysLib's metrological requirement list. Its scorecard is this part's "weaker system"
column: every verdict quoted here is one that file re-derives, and its physics is written
down there. The tutorial adds the walk of the square the case study lacks, with every
number an integer so that each aggregation fact is decided rather than approximated.

Every line of code in this part is quoted live from a module of the `Tutorial` library
(`examples/Tutorial/` in the source tree), and the build refuses a chapter whose quotation
no longer matches its source. Those modules are the starter files: a reader copies one and
replaces the oscillator. Positive claims are `example`s and `theorem`s; every refusal is
pinned with the error the elaborator prints, so a line is shown to be refused _for the
stated reason_ and not by a typo. The square walk imports only the Mathlib-free core; a
chapter that needs the dimension layer or a proof at `ℝ` says so when it begins.

{include 1 PropertyKindCalculusBlueprint.Chapters.Tutorial.T0_OneNumberTwoKinds}

{include 1 PropertyKindCalculusBlueprint.Chapters.Tutorial.T1_Objects}
