-- | Properties of the row solver.
-- |
-- | The generators draw from a small fixed alphabet of variables, labels, and
-- | effect constructors, so that collisions between keys and between tails
-- | arise often rather than by chance.
module Test.Dawn.Compiler.TypedCore.RowProperties (spec) where

import Prelude

import Prim as P

import Dawn.Compiler.TypedCore (Constraint(..), EffName(..), Label(..), ModuleName(..), Qualified(..), RowEntry(..), RowKey(..), TyName(..), TyVar(..), Type(..), decompose, entails, nf, rowEquiv)
import Data.Array as Array
import Data.Array.NonEmpty as NEA
import Data.Either (Either(..), isRight)
import Data.Foldable (all)
import Data.Traversable (sequence)
import Effect.Class (liftEffect)
import Test.QuickCheck (Result, quickCheck, withHelp, (<?>))
import Test.QuickCheck.Gen (Gen, arrayOf, chooseInt, elements, oneOf, resize, sized, suchThat)
import Test.Spec (Spec, describe, it)

prim :: ModuleName
prim = ModuleName "Prim"

genTyVar :: Gen TyVar
genTyVar = elements (NEA.cons' (TyVar "r") [ TyVar "s", TyVar "e" ])

genLabel :: Gen Label
genLabel = elements (NEA.cons' (Label "name") [ Label "age", Label "id" ])

genEffName :: Gen (Qualified EffName)
genEffName = elements
  ( NEA.cons' (Qualified prim (EffName "Console"))
      [ Qualified prim (EffName "State"), Qualified prim (EffName "Exn") ]
  )

genPayloadType :: Gen Type
genPayloadType = elements
  ( NEA.cons' (TCon (Qualified prim (TyName "Int")) [])
      [ TCon (Qualified prim (TyName "String")) [] ]
  )

-- | A row whose known keys are sharp, so that `nf` succeeds on it.
-- |
-- | This is weaker than well-kindedness, which the generators do not establish:
-- | `r ⊎ r` normalizes, and so does `( name : Int | r )` with nothing to
-- | discharge `name ∉ r`. Generating genuinely well-kinded rows means
-- | generating the side-condition facts alongside them. What the properties
-- | below need is that normalization succeeds.
normalizable :: Type -> P.Boolean
normalizable = isRight <<< nf

-- | A normalizable row at `Row Type`. The size bounds how many extensions and
-- | unions are built, so generation terminates.
genRecordRow :: Gen Type
genRecordRow = suchThat rawRecordRow normalizable

rawRecordRow :: Gen Type
rawRecordRow = sized go
  where
  go size
    | size <= 0 = oneOf (NEA.cons' (pure TRowEmpty) [ TVar <$> genTyVar ])
    | otherwise = oneOf
        ( NEA.cons' (pure TRowEmpty)
            [ TVar <$> genTyVar
            , TRowExtend <$> (RowField <$> genLabel <*> genPayloadType) <*> resize (size - 1) rawRecordRow
            , TRowUnion <$> resize (size / 2) rawRecordRow <*> resize (size / 2) rawRecordRow
            ]
        )

-- | A normalizable row at `Row Effect`, whose elements carry no label.
genEffectRow :: Gen Type
genEffectRow = suchThat rawEffectRow normalizable

rawEffectRow :: Gen Type
rawEffectRow = sized go
  where
  go size
    | size <= 0 = oneOf (NEA.cons' (pure TRowEmpty) [ TVar <$> genTyVar ])
    | otherwise = oneOf
        ( NEA.cons' (pure TRowEmpty)
            [ TVar <$> genTyVar
            , TRowExtend <$> (RowEffectEntry <$> genEffName <*> arrayOf genPayloadType) <*> resize (size - 1) rawEffectRow
            , TRowUnion <$> resize (size / 2) rawEffectRow <*> resize (size / 2) rawEffectRow
            ]
        )

genRow :: Gen Type
genRow = oneOf (NEA.cons' genRecordRow [ genEffectRow ])

-- | A constraint over one row kind. A constraint spanning two row kinds is
-- | ill-formed, so both sides are drawn from one generator.
genConstraint :: Gen Constraint
genConstraint = oneOf
  ( NEA.cons' (Lacks <$> (FieldKey <$> genLabel) <*> genRecordRow)
      [ Lacks <$> (EffectKey <$> genEffName) <*> genEffectRow
      , Disjoint <$> genRecordRow <*> genRecordRow
      , Disjoint <$> genEffectRow <*> genEffectRow
      ]
  )

genContext :: Gen (P.Array Constraint)
genContext = do
  n <- chooseInt 0 4
  sequence (Array.replicate n genConstraint)

-- | `decompose Γ = Right Γ*` and `C ∈ Γ` imply `Γ* ⊨ C`.
-- |
-- | An assumption entails itself. A context whose assumptions contradict a
-- | known key fails to decompose and is excluded, having no `Γ*`.
assumptionEntailsItself :: Gen Result
assumptionEntailsItself = do
  context <- genContext
  pure case decompose context of
    Left _ ->
      withHelp true "a contradictory context is excluded"
    Right facts ->
      all (\c -> entails facts c == Right true) context
        <?> ("an assumption is not entailed by the context it came from: " <> show context)

-- | A row is equal to itself.
rowEqualToItself :: Gen Result
rowEqualToItself = do
  row <- genRow
  pure case rowEquiv row row of
    Right true -> withHelp true "reflexive"
    other -> withHelp false ("a row is not equal to itself: " <> show row <> " gave " <> show other)

-- | Deciding equality does not depend on the order the two sides are given in.
rowEqualitySymmetric :: Gen Result
rowEqualitySymmetric = do
  left <- genRow
  right <- genRow
  pure
    ( (rowEquiv left right == rowEquiv right left)
        <?> ("the decision is not symmetric: " <> show left <> " against " <> show right)
    )

spec :: Spec Unit
spec = describe "Dawn.Compiler.TypedCore.Row properties" do
  it "entails every assumption of the context it decomposed" do
    liftEffect (quickCheck assumptionEntailsItself)

  it "holds a row equal to itself" do
    liftEffect (quickCheck rowEqualToItself)

  it "decides row equality independently of the order of the two sides" do
    liftEffect (quickCheck rowEqualitySymmetric)
