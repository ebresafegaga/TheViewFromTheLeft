module DataStore

import Data.Vect

infixr 5 .+.

public export
data Schema = SString | SInt | (.+.) Schema Schema

public export
SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType (x .+. y) = (SchemaType x, SchemaType y)


record DataStore (schema : Schema) where
    constructor MkData
    size : Nat
    items : Vect size (SchemaType schema)


empty : DataStore schema
empty = MkData 0 []


addToStore : (value : SchemaType schema) -> (store : DataStore schema) -> DataStore schema
addToStore value (MkData size items) = MkData (S size) (value :: items)

nil : Vect 0 a
nil = []

data StoreView : DataStore schema -> Type where
    SNil : StoreView nil
    SAdd : (rec : StoreView store) -> StoreView (addToStore value store)

storeViewHelp : (items : Vect size (SchemaType schema)) -> StoreView (MkData size items)
storeViewHelp [] = SNil
storeViewHelp (x :: xs) = SAdd $ storeViewHelp xs

storeView : (store : DataStore schema) -> StoreView store
storeView (MkData size items) = storeViewHelp items

listItems : DataStore schema -> List (SchemaType schema)
listItems input with (storeView input)
    listItems input                    | SNil       = []
    listItems (addToStore value store) | (SAdd rec) = value :: listItems store | rec


filterKeys : (test : SchemaType s -> Bool) -> DataStore (SString .+. s) -> List String
filterKeys test input with (storeView input)
    filterKeys test input                    | SNil       = ?filterKeys_rhs_rhs_1
    filterKeys test (addToStore value store) | (SAdd rec) = ?filterKeys_rhs_rhs_2


export
data Shape = Triangle Double Double
           | Rectangle Double Double
           | Circle Double

export
triangle : Double -> Double -> Shape
triangle = Triangle

export
rectangle : Double -> Double -> Shape
rectangle = Rectangle

export
circle : Double -> Shape
circle = Circle

data ShapeView : Shape -> Type where
    TriangleView : (x : Double) -> (y : Double) -> ShapeView (triangle x y)
    RectangleView : (x : Double) -> (y : Double) -> ShapeView (rectangle x y)
    CircleView : (x : Double) -> ShapeView (circle x)

shapeView : (shape : Shape) -> ShapeView shape
shapeView (Triangle x y)  = TriangleView x y
shapeView (Rectangle x y) = RectangleView x y
shapeView (Circle x)      = CircleView x

area : Shape -> Double
area shape with (shapeView shape)
    area (triangle x y)  | (TriangleView x y)  = ?area_rhs_rhs_1
    area (rectangle x y) | (RectangleView x y) = ?area_rhs_rhs_2
    area (circle x)      | (CircleView x)      = ?area_rhs_rhs_3

    
