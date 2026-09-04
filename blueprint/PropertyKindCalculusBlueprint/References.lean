import VersoManual
open Verso.Genre.Manual

def sysml12 : Article where
  authors := #[inlines!"OMG SysML 1.2 Revision Task Force"]
  journal := inlines!""
  title   := inlines!"Systems Modeling Language, Version 1.2"
  year    := 2010
  month   := some inlines!"June"
  volume  := inlines!""
  number  := inlines!""
  url     := some "https://www.omg.org/spec/SysML/1.2"

def sysml14 : Article where
  authors := #[inlines!"OMG SysML 1.4 Revision Task Force"]
  journal := inlines!""
  title   := inlines!"Systems Modeling Language, Version 1.4"
  year    := 2015
  month   := some inlines!"August"
  volume  := inlines!""
  number  := inlines!""
  url     := some "https://www.omg.org/spec/SysML/1.5"

def sysml20 : Article where
  authors := #[inlines!"OMG SysML 2.0 Finalization Task Force"]
  journal := inlines!""
  title   := inlines!"Systems Modeling Language, Version 2.0"
  year    := 2025
  month   := some inlines!"September"
  volume  := inlines!""
  number  := inlines!""
  url     := some "https://www.omg.org/spec/SysML/2.0"

def foster_automated_reasoning_for_physical_quantities : Article where
  authors := #[inlines!"Simon Foster", inlines!"Burkhart Wolff"]
  journal := inlines!"27th International Conference on Engineering of Complex Computer Systems (ICECCS)"
  title   := inlines!"Automated Reasoning for Physical Quantities, Units, and Measurements in Isabelle/HOL"
  year    := 2023
  month   := none
  volume  := inlines!""
  number  := inlines!""
  url     := some "https://isa-afp.org/browser_info/current/AFP/Physical_Quantities/"

def george_torchlean_formalizing_neural_networks : Article where
  authors := #[inlines!"Robert Joseph George", inlines!"Jennifer Cruden", inlines!"Will Adkisson",
               inlines!"Xiangru Zhong", inlines!"Huan Zhang", inlines!"Anima Anandkumar"]
  journal := inlines!"arXiv preprint arXiv:2602.22631 (cs.MS)"
  title   := inlines!"TorchLean: Formalizing Neural Networks in Lean"
  year    := 2026
  month   := none
  volume  := inlines!""
  number  := inlines!""
  url     := some "https://arxiv.org/abs/2602.22631"


def dybkaer_units_for_quantities_of_dimension_one : Article where
  authors := #[inlines!"René Dybkær"]
  journal := inlines!"Metrologia"
  title   := inlines!"Units for quantities of dimension one"
  year    := 2004
  month   := none
  volume  := inlines!"41"
  number  := inlines!"1"
  url     := some "https://iopscience.iop.org/article/10.1088/0026-1394/41/1/010"

-- Verso has no Book entry type; publisher in the journal slot is this file's convention
-- for non-journal items (see the SysML specs above). Bibliographic data human-verified
-- (AI-POLICY §2.1): supplied by Nicolas Rouquette, 2026-09-04, from the OUP record.
-- The three chapter entries below it are verified against the vendored volume's own title
-- and copyright pages (References/ontology-modality-and-mind-…​.pdf: OUP, 2018,
-- ISBN 978-0-19-879629-9, eds. Carruth, Gibb, Heil); each chapter's title and author are
-- read from that volume's table of contents and its own chapter opening page.
def simons_basis_of_categorial_distinctions : InProceedings where
  title := inlines!"Lowe, the Primacy of Metaphysics, and the Basis of Categorial Distinctions"
  authors := #[inlines!"Peter Simons"]
  year := 2018
  booktitle := inlines!"Ontology, Modality, and Mind: Themes from the Metaphysics of E. J. Lowe (Oxford University Press)"
  editors := some #[inlines!"Alexander Carruth", inlines!"Sophie Gibb", inlines!"John Heil"]

def heil_existents_and_universals : InProceedings where
  title := inlines!"Existents and Universals"
  authors := #[inlines!"John Heil"]
  year := 2018
  booktitle := inlines!"Ontology, Modality, and Mind: Themes from the Metaphysics of E. J. Lowe (Oxford University Press)"
  editors := some #[inlines!"Alexander Carruth", inlines!"Sophie Gibb", inlines!"John Heil"]
/-- Chapter 4 of the volume; it opens at p. 60, and chapter 5 opens at p. 73. -/
def marmodoro_whole_but_not_one : InProceedings where
  title := inlines!"Whole, but not One"
  authors := #[inlines!"Anna Marmodoro"]
  year := 2018
  booktitle := inlines!"Ontology, Modality, and Mind: Themes from the Metaphysics of E. J. Lowe (Oxford University Press)"
  editors := some #[inlines!"Alexander Carruth", inlines!"Sophie Gibb", inlines!"John Heil"]

def lowe_four_category_ontology : Article where
  authors := #[inlines!"E. J. Lowe"]
  journal := inlines!"Oxford University Press"
  title   := inlines!"The Four-Category Ontology: A Metaphysical Foundation for Natural Science"
  year    := 2005
  month   := some inlines!"December"
  volume  := inlines!""
  number  := inlines!""
  url     := some "https://doi.org/10.1093/0199254397.001.0001"

def dybkaer_ontology_on_property : Thesis where
  author      := inlines!"René Dybkær"
  degree      := inlines!"PhD Thesis"
  title       := inlines!"An Ontology on Property for Physical, Chemical, and Biological Systems"
  university  := inlines!"University of Copenhagen"
  year        := 2004
  url         := some "https://ontology.iupac.org/"

def flater_architecture_for_software_assisted_quantity_calculus : Article where
  authors   := #[inlines!"David Flater"]
  journal   := inlines!"Computer Standards & Interfaces"
  title     := inlines!"Architecture for software-assisted quantity calculus"
  year      := 2018
  month     := none
  volume    := inlines!"56"
  number    := inlines!""
  url       := some "https://doi.org/10.6028/NIST.TN.1943"

def dimensionless_units_in_the_si : Article where
  authors   := #[inlines!"Peter J. Mohr", inlines!"William D. Phillips"]
  journal   := inlines!"Metrologia"
  title     := inlines!"DImensionless units in the SI"
  year      := 2015
  month     := none
  volume    := inlines!"52"
  number    := inlines!"1"
  url       := some "https://iopscience.iop.org/article/10.1088/0026-1394/52/1/40"

def angles_in_the_si_a_practical_dimensional_metrologist_viewpoint : Article where
  authors   := #[inlines!"Andrew J. Lewis", inlines!"Timothy J. Coveney"]
  journal   := inlines!"Metrologia"
  title     := inlines!"Angles in the SI - a practical dimensional metrologist viewpoint"
  year      := 2026
  month     := none
  volume    := inlines!"63"
  number    := inlines!"2"
  url       := some "https://iopscience.iop.org/article/10.1088/1681-7575/ae3dee"

def unit_one_is_intruisive : Article where
  authors   := #[inlines!"David Flater"]
  journal   := inlines!"Metrologia"
  title     := inlines!"Unit one is intrusive"
  year      := 2024
  month     := none
  volume    := inlines!"61"
  number    := inlines!"3"
  url       := some "https://iopscience.iop.org/article/10.1088/1681-7575/ad4bea"

def quincey_angles_neither_length_ratios_nor_dimensionless : Article where
  authors   := #[inlines!"Paul Quincey", inlines!"Peter J. Mohr", inlines!"William D. Phillips"]
  journal   := inlines!"Metrologia"
  title     := inlines!"Angles are inherently neither length ratios nor dimensionless"
  year      := 2019
  month     := none
  volume    := inlines!"56"
  number    := inlines!"4"
  url       := some "https://iopscience.iop.org/article/10.1088/1681-7575/ab27d7"

def leonard_dimensionally_consistent_treatment_of_angle_and_solid_angle : Article where
  authors   := #[inlines!"B. P. Leonard"]
  journal   := inlines!"Metrologia"
  title     := inlines!"Proposal for the dimensionally consistent treatment of angle and solid angle by the International System of Units (SI)"
  year      := 2021
  month     := none
  volume    := inlines!"58"
  number    := inlines!"5"
  url       := some "https://iopscience.iop.org/article/10.1088/1681-7575/abe0fc"

def willink_evaluation_of_measurement_uncertainty_based_on_moments : Article where
  authors   := #[inlines!"Robin Willink"]
  journal   := inlines!"Metrologia"
  title     := inlines!"A procedure for the evaluation of measurement uncertainty based on moments"
  year      := 2005
  month     := none
  volume    := inlines!"42"
  number    := inlines!"5"
  url       := some "https://iopscience.iop.org/article/10.1088/0026-1394/42/5/001"

def degenhardt_efficient_alternative_to_monte_carlo : Article where
  authors   := #[inlines!"Johannes Degenhardt", inlines!"Rainer Tutsch", inlines!"Xiukun Hu",
                 inlines!"Gaoliang Dai"]
  journal   := inlines!"Metrologia"
  title     := inlines!"A practically oriented, efficient alternative to the Monte Carlo method for measurement uncertainty estimation"
  year      := 2025
  month     := none
  volume    := inlines!"62"
  number    := inlines!"2"
  url       := some "https://iopscience.iop.org/article/10.1088/1681-7575/adb3ab"
