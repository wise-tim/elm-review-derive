module Internal.Builtin.CodeGenExpr exposing (codeGen)

import CodeGenerator exposing (CodeGenerator)
import Elm.CodeGen as CG
import Elm.Pretty
import Elm.Syntax.Expression
import Elm.Syntax.Node
import Internal.Helpers
import List.Extra
import Maybe.Extra
import Pretty
import ResolvedType
import Set
import String.Extra
import TypePattern exposing (TypePattern(..))


debug expr =
    let
        _ =
            Debug.log ("\nExpr:\n" ++ (Elm.Pretty.prettyExpression expr |> Pretty.pretty 120)) ()
    in
    expr


keywords =
    Set.fromList
        [ "if"
        , "then"
        , "else"
        , "case"
        , "of"
        , "let"
        , "in"
        , "type"
        , "module"
        , "where"
        , "import"
        , "exposing"
        , "as"
        , "port"
        ]


makeValueName name =
    let
        lower =
            String.Extra.decapitalize name
    in
    if Set.member lower keywords then
        lower ++ "_"

    else
        lower


codeGen : CodeGenerator
codeGen =
    CodeGenerator.define
        { id = "mdgriffith/elm-codegen/Elm"
        , dependency = "mdgriffith/elm-codegen"
        , typePattern = Function Target (Typed [ "Elm" ] "Expression" [])
        , makeName = \name -> String.Extra.decapitalize name ++ "Expression"
        }
        [ CodeGenerator.string (CG.fqFun [ "Elm" ] "string")
        , CodeGenerator.int (CG.fqFun [ "Elm" ] "int")
        , CodeGenerator.float (CG.fqFun [ "Elm" ] "float")
        , CodeGenerator.bool (CG.fqFun [ "Elm" ] "bool")
        , CodeGenerator.char (CG.fqFun [ "Elm" ] "char")
        , CodeGenerator.customType
            (\constructors expressions ->
                CG.lambda [ CG.varPattern "value" ]
                    (List.map2
                        (\( ref, args ) ( _, expr ) ->
                            ( CG.fqNamedPattern ref.modulePath
                                ref.name
                                (args |> List.indexedMap (\i _ -> CG.varPattern ("arg" ++ String.fromInt i)))
                            , case args of
                                [] ->
                                    CG.access
                                        (CG.fqFun ("Gen" :: ref.modulePath) "make_")
                                        (makeValueName ref.name)

                                _ ->
                                    CG.apply (expr :: thingsToValues args 0)
                            )
                        )
                        constructors
                        expressions
                        |> CG.caseExpr (CG.val "value")
                     -- |> debug
                    )
            )
        , CodeGenerator.customDict
            (\( keyType, keyEncoder ) ( valType, valEncoder ) ->
                CG.lambda [ CG.varPattern "dict" ]
                    (CG.apply
                        [ CG.fqFun [ "Gen", "Dict" ] "fromList"
                        , CG.pipe (CG.val "dict")
                            [ CG.fqFun [ "Dict" ] "toList"
                            , CG.apply
                                [ CG.fqFun [ "List" ] "map"
                                , CG.lambda [ CG.tuplePattern [ CG.varPattern "k", CG.varPattern "v" ] ]
                                    (CG.apply
                                        [ CG.fqFun [ "Elm" ] "tuple"
                                        , CG.apply [ keyEncoder, CG.val "k" ]
                                        , CG.apply [ valEncoder, CG.val "v" ]
                                        ]
                                    )
                                ]
                            ]
                        ]
                    )
            )
        , CodeGenerator.maybe
            (\a ->
                CG.lambda [ CG.varPattern "maybe" ]
                    (CG.apply
                        [ CG.pipe (CG.val "maybe")
                            [ CG.apply
                                [ CG.fqFun [ "Maybe" ] "map"
                                , a
                                ]
                            , CG.fqFun [ "Elm" ] "maybe"
                            ]
                        ]
                    )
            )
        , CodeGenerator.list
            (\a ->
                CG.lambda [ CG.varPattern "list" ]
                    (CG.apply
                        [ CG.pipe (CG.val "list")
                            [ CG.apply
                                [ CG.fqFun [ "List" ] "map"
                                , a
                                ]
                            , CG.fqFun [ "Elm" ] "list"
                            ]
                        ]
                    )
            )
        , CodeGenerator.set
            (\a ->
                CG.lambda [ CG.varPattern "set" ]
                    (CG.apply
                        [ CG.pipe (CG.val "set")
                            [ CG.apply
                                [ CG.fqFun [ "Set" ] "toList"
                                , a
                                ]
                            , CG.fqFun [ "Gen", "Set" ] "fromList"
                            ]
                        ]
                    )
            )
        , CodeGenerator.combiner combiner
        ]


combiner : ResolvedType.ResolvedType -> CG.Expression -> List CG.Expression -> Maybe CG.Expression
combiner t constructor exprs =
    case
        t
    of
        ResolvedType.AnonymousRecord _ fields ->
            Internal.Helpers.lambda1 "rec"
                (\rec ->
                    CG.apply
                        [ CG.fqFun [ "Elm" ] "record", CG.list (List.map2 (\( field, _ ) expr -> CG.tuple [ CG.string field, CG.apply [ expr, CG.access rec field ] ]) fields exprs) ]
                )
                |> Just

        ResolvedType.Opaque ref vars ->
            Just
                (CG.lambda (thingsToPatterns exprs 10)
                    (CG.apply
                        (CG.access
                            (CG.fqFun ("Gen" :: ref.modulePath) "make_")
                            (makeValueName ref.name)
                            :: List.indexedMap (\i ( expr, arg ) -> CG.apply [ expr, arg ]) (List.map2 Tuple.pair exprs (thingsToValues exprs 10))
                        )
                    )
                )

        ResolvedType.TypeAlias _ _ def ->
            combiner def constructor exprs

        ResolvedType.GenericType name ref ->
            Just constructor

        ResolvedType.Tuple args ->
            case exprs of
                [ fst, snd ] ->
                    Internal.Helpers.lambda1 "tuple"
                        (\tuple ->
                            CG.apply
                                [ CG.fqFun [ "Elm" ] "tuple"
                                , CG.apply [ fst, CG.apply [ CG.fqFun [ "Tuple" ] "first", tuple ] ]
                                , CG.apply [ snd, CG.apply [ CG.fqFun [ "Tuple" ] "second", tuple ] ]
                                ]
                        )
                        |> Just

                [ fst, snd, thrd ] ->
                    Internal.Helpers.lambda1 "triple"
                        (\triple ->
                            CG.letExpr [ CG.letDestructuring (CG.tuplePattern [ CG.varPattern "first", CG.varPattern "second", CG.varPattern "third" ]) triple ]
                                (CG.apply
                                    [ CG.fqFun [ "Elm" ] "triple"
                                    , CG.apply [ fst, CG.val "first" ]
                                    , CG.apply [ snd, CG.val "second" ]
                                    , CG.apply [ thrd, CG.val "third" ]
                                    ]
                                )
                        )
                        |> Just

                _ ->
                    Nothing

        _ ->
            Nothing


thingsToPatterns : List a -> Int -> List CG.Pattern
thingsToPatterns list int =
    list |> List.indexedMap (\i _ -> CG.varPattern ("arg" ++ String.fromInt (i + int)))


thingsToValues : List a -> Int -> List CG.Expression
thingsToValues list int =
    list |> List.indexedMap (\i _ -> CG.val ("arg" ++ String.fromInt (i + int)))
