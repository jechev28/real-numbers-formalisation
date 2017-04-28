module README where

-- Inductively defines the type of natural numbers and operations of
-- addition and multiplication under this type.
open import Nat.agda

-- It shows the convergence of some series in the real numbers.
open import SeriesExamples.agda

-- The empty set is defined and the proof is shown that it is bounded.
open import BoundedEmptySet.agda

-- Equation reasoning is defined.
open import EqReasoning.agda

-- Equation reasoning is defined for the "greater or equal" relationship.
open import PoReasoning.agda

-- Proof of the properties of equality (_≡_).
open import EqProperties.agda

-- It defines the basic concepts of logic that are used in this thesis.
open import LogicDefinitions.agda

-- Theorems that depend on the order axioms, with their respective
-- ATP-pragma, are proposed for their automatic demonstration.
open import OrderedFieldPropertiesATP.agda

-- -- It proves the properties that satisfies the absolute value.
open import AbsoluteValueProperties.agda

-- Some properties of logic are proved.
open import LogicProperties.agda

-- Properties are proposed on Distance between two points, with
-- their respective ATP-pragma, for their automatic demonstration.
open import DistancePropertiesATP.agda

-- The properties of the Distance between two points function are
-- proved.
open import DistanceProperties.agda

-- Some examples are made using the Completeness axiom and the
-- definitions of: Upper bound, Bounded set and Supreme set.
open import Completeness.agda

-- It is proved the "De Morgan's laws".
open import DemorganLaws.agda

-- The Distance between two points function is defined.
open import DistanceDefinition.agda

-- The absolute value function is defined.
open import AbsoluteValueDefinition.agda

-- In this file the axioms of field, of order and of completeness are
-- posited; And the definitions they require.
open import RealNumbersAxioms.agda

-- Properties that depend on the axioms of order and in particular the
-- axiom of tricotomy are proposed, to be demonstrated automatically.
open import TrichotomyPropertiesATP.agda

-- The proof of some theorems is made from the axioms of field and order.
open import OrderedFieldProperties.agda

-- Algunas propiedades de los Límites de una función son probadas.
open import Limit.agda

-- Se postula la ley del tercio excluido y se demuestran algunas
-- propiedades que dependen de él.
open import ClassicLogic.agda

-- Potentiation is defined for real numbers with natural exponents and
-- some of their laws are proved.
open import Exp.agda

-- The function "Minimum between two real" is defined and some
-- properties are demonstrated that this function fulfills.
open import Min.agda



