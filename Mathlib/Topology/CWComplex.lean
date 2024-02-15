import Mathlib.Topology.ContinuousFunction.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Category.TopCat.Limits.Products
import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
import Mathlib.Topology.Order
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Pullbacks
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Analysis.InnerProductSpace.PiL2

open CategoryTheory


namespace CWComplex
noncomputable section

/- sphere in ℝⁿ with radius 1 -/
notation:0 "𝕊" n => Metric.sphere (0 : EuclideanSpace ℝ <| Fin <| n + 1) 1
/- open ball in ℝⁿ with radius 1 -/
notation:0 "𝔹" n => Metric.ball (0 : EuclideanSpace ℝ <| Fin n) 1
/- closed ball (disc) in ℝⁿ with radius 1 -/
notation:0 "𝔻" n => Metric.closedBall (0 : EuclideanSpace ℝ <| Fin n) 1

--universe u v w x
--variable {F : Type*} {X : Type u} {X' : Type v} {Y : Type w} {Z : Type x} {ι : Type*}
--variable [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y]

def CellBorderInclusion (n : ℕ) : (𝕊 n) → (𝔻 n + 1) := fun ⟨pt, hpt⟩ => ⟨pt, le_of_eq hpt⟩

theorem continuous_cellBorderInclusion (n : ℕ) : Continuous (CellBorderInclusion n) :=
  ⟨by
    intro s hs
    rw [isOpen_induced_iff] at *
    obtain ⟨t, ht, ht'⟩ := hs
    use t, ht
    rw [ht'.symm]
    ext ⟨xval, xprop⟩
    repeat
      rw [Set.mem_preimage]
    constructor
    repeat
      intro h
      dsimp [CellBorderInclusion] at *
      exact h
  ⟩

def SigmaCellBorderInclusion (n : ℕ) (cells : Type) :
    (Σ (_ : cells), 𝕊 n) → (Σ (_ : cells), 𝔻 n + 1) :=
  Sigma.map id fun _ x => CellBorderInclusion n x

theorem continuous_sigmaCellBorderInclusion (n : ℕ) (cells : Type) :
    Continuous (SigmaCellBorderInclusion n cells) := by
  apply Continuous.sigma_map
  intro _
  apply continuous_cellBorderInclusion

def BundledSigmaCellBorderInclusion (n : ℕ) (cells : Type) :
    ContinuousMap (TopCat.of (Σ (_ : cells), 𝕊 n)) (TopCat.of (Σ (_ : cells), 𝔻 n + 1)) :=
  ⟨SigmaCellBorderInclusion n cells, continuous_sigmaCellBorderInclusion n cells⟩

def SigmaAttachMap (X : TopCat) (n : ℕ) (cells : Type)
    (attach_maps : cells → ContinuousMap (𝕊 n) X) :
    (Σ (_ : cells), 𝕊 n) → X :=
  fun ⟨i, x⟩ => attach_maps i x

theorem continuous_sigmaAttachMap (X : TopCat) (n : ℕ) (cells : Type)
    (attach_maps : cells → ContinuousMap (𝕊 n) X) :
    Continuous (SigmaAttachMap X n cells attach_maps) := by
  apply continuous_sigma
  exact fun i => (attach_maps i).continuous_toFun

def BundledSigmaAttachMap (X : TopCat) (n : ℕ) (cells : Type)
    (attach_maps : cells → ContinuousMap (𝕊 n) X) :
    ContinuousMap (TopCat.of (Σ (_ : cells), 𝕊 n)) X :=
  ⟨SigmaAttachMap X n cells attach_maps, continuous_sigmaAttachMap X n cells attach_maps⟩

-- A type witnessing that X' is obtained from X by attaching n-cells
structure AttachCells (X X' : TopCat) (n : ℕ) where
  /- The index type over n-cells -/
  cells : Type
  attach_maps : cells → ContinuousMap (𝕊 n) X
  iso_pushout : X' ≅ Limits.pushout
    (BundledSigmaCellBorderInclusion n cells)
    (BundledSigmaAttachMap X n cells attach_maps)

end
end CWComplex

-- structure CWComplex where
--   /- Skeleta -/
--   sk : ℤ → TopCat
--   /- Every n-skeleton for n < 0 is empty. -/
--   sk_neg_empty : ∀ n < 0, sk n = Empty
--   /- For n ≥ 0, the (n-1)-skeleton is obtained from the n-skeleton by attaching n-cells. -/
--   attach_cells : (n : ℕ) → AttachCells (sk (n - 1)) (sk n) n

--variable {X : Type}

--class CWComplex (X : Type u) where
structure CWComplex where
  /- Skeleta -/
  sk : ℕ → TopCat
  /- The 0-skeleton is a discrete topological space. -/
  discrete_sk_zero : DiscreteTopology (sk 0)
  /- The (n+1)-skeleton is obtained from the n-skeleton by attaching (n+1)-cells. -/
  attach_cells : (n : ℕ) → CWComplex.AttachCells (sk n) (sk (n + 1)) (n + 1)


namespace CWComplex
noncomputable section

-- The inclusion map from X to X', given that X' is obtained from X by attaching n-cells
def AttachCellsInclusion (X X' : TopCat) (n : ℕ) (att : AttachCells X X' n) : X ⟶ X'
  := @Limits.pushout.inr TopCat _ _ _ X
      (BundledSigmaCellBorderInclusion n att.cells)
      (BundledSigmaAttachMap X n att.cells att.attach_maps) _ ≫ att.iso_pushout.inv

-- The inclusion map from the n-skeleton to the (n+1)-skeleton of a CW-complex
def SkeletaInclusion (X : CWComplex) (n : ℕ) : X.sk n ⟶ X.sk (n + 1) :=
  AttachCellsInclusion (X.sk n) (X.sk (n + 1)) (n + 1) (X.attach_cells n)

-- The inclusion map from the n-skeleton to the m-skeleton of a CW-complex
-- Note: A dependently-typed `List` with `List.range'` and `List.foldl_assoc` could help here.
-- Does mathlib have that?
def SkeletaInclusion' (X : CWComplex) (n : ℕ) (m : ℕ) (n_le_m : n ≤ m) :
    X.sk n ⟶ X.sk m :=
  if h : n = m then by
    rw [<- h]
    exact 𝟙 (X.sk n)
  else by
    have : n < m := Nat.lt_of_le_of_ne n_le_m h
    exact SkeletaInclusion X n ≫ SkeletaInclusion' X (n + 1) m this
  termination_by _ => m - n

def ColimitDiagram (X : CWComplex) : ℕ ⥤ TopCat where
  obj := X.sk
  map := @fun n m n_le_m => SkeletaInclusion' X n m <| Quiver.Hom.le n_le_m
  map_id := by
    unfold SkeletaInclusion'
    aesop
  map_comp := by
    intro n m l n_le_m m_le_l
    have n_le_m := Quiver.Hom.le n_le_m
    have m_le_l := Quiver.Hom.le m_le_l
    exact p n m l n_le_m m_le_l (Nat.le_trans n_le_m m_le_l)
    where
      p (n m l : ℕ) (n_le_m : n ≤ m) (m_le_l : m ≤ l) (n_le_l : n ≤ l) :
        SkeletaInclusion' X n l n_le_l =
        SkeletaInclusion' X n m n_le_m ≫
        SkeletaInclusion' X m l m_le_l :=
      if hnm : n = m then by
        unfold SkeletaInclusion'
        aesop
      else by
        have h1 : n < m := Nat.lt_of_le_of_ne n_le_m hnm
        have h2 : n < l := by linarith
        unfold SkeletaInclusion'
        simp [hnm, Nat.ne_of_lt h2]
        rcases em (m = l) with hml | hml
        . aesop
        congr
        rw [p (n + 1) m l h1 m_le_l h2]
        congr
        simp [hml]
        conv => lhs; unfold SkeletaInclusion'
        simp [hml]
      termination_by _ => l - n

-- The topology on a CW-complex.
def toTopCat (X : CWComplex) : TopCat := Limits.colimit (ColimitDiagram X)

instance : Coe CWComplex TopCat where coe X := toTopCat X

end
end CWComplex
