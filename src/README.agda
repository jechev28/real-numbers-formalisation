module README where

-- Inductively defines the type of natural numbers and operations of
-- addition and multiplication under this type.
open import Nat

-- It shows the convergence of some series in the real numbers.
open import SeriesExamples

-- The empty set is defined and the proof is shown that it is bounded.
open import BoundedEmptySet

-- Equation reasoning is defined.
open import EqReasoning

-- Equation reasoning is defined for the "greater or equal" relationship.
open import PoReasoning

-- Proof of the properties of equality (_≡_).
open import EqProperties

-- It defines the basic concepts of logic that are used in this thesis.
open import LogicDefinitions

-- Theorems that depend on the order axioms, with their respective
-- ATP-pragma, are proposed for their automatic demonstration.
open import OrderedFieldPropertiesATP

-- -- It proves the properties that satisfies the absolute value.
open import AbsoluteValueProperties

-- Some properties of logic are proved.
open import LogicProperties

-- Properties are proposed on Distance between two points, with
-- their respective ATP-pragma, for their automatic demonstration.
open import DistancePropertiesATP

-- The properties of the Distance between two points function are
-- proved.
open import DistanceProperties

-- Some examples are made using the Completeness axiom and the
-- definitions of: Upper bound, Bounded set and Supreme set.
open import Completeness

-- It is proved the "De Morgan's laws".
open import DemorganLaws

-- The Distance between two points function is defined.
open import DistanceDefinition

-- The absolute value function is defined.
open import AbsoluteValueDefinition

-- In this file the axioms of field, of order and of completeness are
-- posited; And the definitions they require.
open import RealNumbersAxioms

-- Properties that depend on the axioms of order and in particular the
-- axiom of tricotomy are proposed, to be demonstrated automatically.
open import TrichotomyPropertiesATP

-- The proof of some theorems is made from the axioms of field and order.
open import OrderedFieldProperties

-- Algunas propiedades de los Límites de una función son probadas.
open import Limit

-- Se postula la ley del tercio excluido y se demuestran algunas
-- propiedades que dependen de él.
open import ClassicLogic

-- Potentiation is defined for real numbers with natural exponents and
-- some of their laws are proved.
open import Exp

-- The function "Minimum between two real" is defined and some
-- properties are demonstrated that this function fulfills.
open import Min


