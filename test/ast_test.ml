open! Core
open! Uniparse
open! Uniparse.Let_syntax

module Ast = struct
  module Variable = struct
    type t = Uchar.t

    let sexp_of_t t = Sexp.Atom (Uchar.Utf8.to_string t)

    let of_quickcheckable uchar =
      if Uucp.Alpha.is_alphabetic uchar then Some uchar else None
    ;;

    let to_quickcheckable t = t

    include functor Quickcheckable.Of_quickcheckable_filtered (Uchar)
  end

  type t =
    | Number of (int[@quickcheck.generator Quickcheck.Generator.small_non_negative_int])
    | Variable of Variable.t
    | Add of t * t
    | Mul of t * t
  [@@deriving variants, sexp_of, quickcheck]

  let rec to_string' t =
    match t with
    | Number n -> Int.to_string n, ~loose_addition:false
    | Variable v -> Uchar.Utf8.to_string v, ~loose_addition:false
    | Add (t1, t2) ->
      let s1, ~loose_addition:_ = to_string' t1 in
      let s2, ~loose_addition:_ = to_string' t2 in
      s1 ^ " + " ^ s2, ~loose_addition:true
    | Mul (t1, t2) ->
      let s1 = to_string_non_loose t1 in
      let s2 = to_string_non_loose t2 in
      s1 ^ " * " ^ s2, ~loose_addition:false

  and to_string_non_loose t =
    let s, ~loose_addition = to_string' t in
    if loose_addition then "(" ^ s ^ ")" else s
  ;;

  let to_string t =
    let s, ~loose_addition:_ = to_string' t in
    s
  ;;
end

let parse_number =
  fold_while
    ~f:(fun acc char ->
      match Uchar.to_char char with
      | None -> Null
      | Some char ->
        (match Char.get_digit char with
         | Some n -> This ((acc * 10) + n)
         | None -> Null))
    ~init:0
  |> nonempty
;;

let variable = satisfy Uucp.Alpha.is_alphabetic
let whitespace = skip_while Uucp.White.is_white_space
let open_parenthesis = satisfy (Uchar.equal (Uchar.of_char '('))
let close_parenthesis = satisfy (Uchar.equal (Uchar.of_char ')'))
let add = satisfy (Uchar.equal (Uchar.of_char '+'))
let mul = satisfy (Uchar.equal (Uchar.of_char '*'))
let number_or_variable = choose [ parse_number >>| Ast.number; variable >>| Ast.variable ]

let parser =
  fix (fun parser ->
    let multiplicative_unit =
      fix (fun multiplicative_unit ->
        let single_unit =
          whitespace
          *> choose
               [ number_or_variable; open_parenthesis *> parser <* close_parenthesis ]
          <* whitespace
        in
        let%mapn left = single_unit
        and right =
          optional
            (optional mul ~default:() ~return:ignore *> multiplicative_unit)
            ~default:None
            ~return:Option.return
        in
        match right with
        | None -> left
        | Some right -> Ast.mul left right)
    in
    let%mapn left = multiplicative_unit
    and right = optional (add *> parser) ~default:None ~return:Option.return in
    match right with
    | None -> left
    | Some right -> Ast.add left right)
;;

let%expect_test _ =
  let input = "1 + 2x * (3 + 4) + 6" in
  parse_string parser input ~consume:`All ~encoding:Utf8
  |> ok_exn
  |> [%sexp_of: Ast.t]
  |> print_s;
  [%expect
    {|
      (Add (Number 1)
       (Add (Mul (Number 2) (Mul (Variable x) (Add (Number 3) (Number 4))))
        (Number 6)))
      |}]
;;

let%expect_test _ =
  Quickcheck.iter ~trials:20 Ast.quickcheck_generator ~f:(fun ast ->
    Ast.to_string ast |> print_endline;
    Ast.to_string ast
    |> parse_string parser ~consume:`All ~encoding:Utf8
    |> ok_exn
    |> [%sexp_of: Ast.t]
    |> print_s);
  [%expect
    {|
      0
      (Number 0)
      ɥ * H
      (Mul (Variable "\201\165") (Variable H))
      (0 + 络) * y
      (Mul (Add (Number 0) (Variable "\231\187\156")) (Variable y))
      1 * 0 + 1 + Þ
      (Add (Mul (Number 1) (Number 0)) (Add (Number 1) (Variable "\195\158")))
      4 * 3 * 0 * 嬦 * (ӄ + 1)
      (Mul (Number 4)
       (Mul (Number 3)
        (Mul (Number 0)
         (Mul (Variable "\229\172\166") (Add (Variable "\211\132") (Number 1))))))
      2
      (Number 2)
      φ
      (Variable "\207\134")
      b * ߪ * (3 + 3 * 3 + 4 * Ϲ)
      (Mul (Variable b)
       (Mul (Variable "\223\170")
        (Add (Number 3)
         (Add (Mul (Number 3) (Number 3)) (Mul (Number 4) (Variable "\207\185"))))))
      E
      (Variable E)
      3
      (Number 3)
      9 + 8 + 0 * (T + 냰)
      (Add (Number 9)
       (Add (Number 8)
        (Mul (Number 0) (Add (Variable T) (Variable "\235\131\176")))))
      11 + 11
      (Add (Number 11) (Number 11))
      𡤬 * (3 * 9 + 10 + ϡ)
      (Mul (Variable "\240\161\164\172")
       (Add (Mul (Number 3) (Number 9)) (Add (Number 10) (Variable "\207\161"))))
      I
      (Variable I)
      15
      (Number 15)
      1 * 誫 + f + (g * (8 + 0 + 9) + 8 * 4) * 11 * 7 + 11 + i
      (Add (Mul (Number 1) (Variable "\232\170\171"))
       (Add (Variable f)
        (Add
         (Mul
          (Add (Mul (Variable g) (Add (Number 8) (Add (Number 0) (Number 9))))
           (Mul (Number 8) (Number 4)))
          (Mul (Number 11) (Number 7)))
         (Add (Number 11) (Variable i)))))
      Փ
      (Variable "\213\147")
      蹚
      (Variable "\232\185\154")
      6 + 謁
      (Add (Number 6) (Variable "\239\170\188"))
      16 + 19
      (Add (Number 16) (Number 19))
      |}]
;;

let expression_large =
  " (862443739 * 981384025 + 991989189) * (999899699 * ((H + (999999981 + c + (999958028 \
   + 999328371) * ((999980997 * j * (632026619 + 999999841 + 999999350 * (Ķ + i * G)) * \
   999999789 * ġ + ߊ + (999999967 + 999999720) * Μ + 999996565) * 쩍 + (һ * (888152593 + \
   4687481 * 999642068 * ڗ * (r + (㑒 + 999998436 * b * 999992099 * (J * (999999841 + 䄮) \
   * (157526090 + (999999785 * 999954712 + 敵 * A * (c * 999996271 * F + 999887728 + س * \
   (999442988 * 998353295 * (ү + (999241744 + 999991856) * ެ) * 894762185 * ᓕ + \
   999999899 + 𮶢 + (799312578 * Γ + 154035502 * 999999942 * 999476517 * (999999861 + \
   999987882) * ص * (997862169 + 멞 + 999999918 + 999999461 + 999985101 + M) * 999999931 \
   * 985154871 * Ἷ) * (885313214 * (ﳘ + 뵶 * ﺚ * ꠒ * (999999942 * (999992433 + x * \
   (999999312 + 999985384 + 뜒)) + 999999943)) * 999979299 + H + s + J * (484668101 + Y * \
   A) * (999999942 + 999999919) * (R + 996316176)) * (998196871 * Y + 𘗆 + 𥸯) * h * B) * \
   n * ʮ + 45379621)) * (秱 + (s * 908969893 * (y + 蚴) * 999999490 + 999999757) * (y * \
   999997655 * (Ꙟ * (900137628 + Φ) + 999965013 + C + N + o) * 999998606 * (㡉 * \
   (999999824 * 999972744 + 996630387 + o) + 852349872 + 999997941 * 999882311) + ((ﺕ + \
   743653466 * ﰋ + y) * 996603931 + 彫 + 𗸩) * 999999327) * 845627049 * Q * 999999713 * Ķ) \
   + O + 룔) + 897722322 * 931550842) * C * (พ * 999995615 + 999999865)) * (p + R * E)) * \
   (腤 * 999999972 + 999921654 * (892067839 + K + q + V))) + (瓘 + 996400942 * (ᧅ + \
   999999969 + (999999769 + E + ࢗ) * 999999870 * 999999897 + 944194501 + 993626226 + \
   999871527) * (B + ﹽ)) * l * 317146659 + 999987902) * 슧 * (989442926 + d)) * 999878574 \
   * ((999983662 + 炋 * 999999970 * (998310488 + N + 999999966 * п) * 999089674 * ɻ + 穖 + \
   999931977 * 999999675 + Ӣ + 999825654 * (p * 999999855 * (f + e) * 999791996 + D) + 덏 \
   + 750485980) * 꾪 + ȋ * j * Ȱ) * 999910002 * E * 999999689 * 999727624) * (ۺ + 濾 * 跐 + \
   (999999589 * 999998575 + ϊ) * 881638576) + u) * ꦮ * 999966188 * (((999999980 + \
   999999906 + 999838575 * j) * 999990744 + 999995135 + ((Z * ȕ * ((999999974 + ٯ * \
   999999115) * (774170422 * 193559086 + 맫) + 칡) * 㚘 + 999999978) * (999680285 + P + (U \
   + ꑕ * (o * 吔 + 柮) * 𠊼) * (밤 + ß + 999999484) * 702410807) + 999862719 + b * 𪯚 + \
   999995862 + ح) * (댧 + f)) * 999874096 + U) * e + 999999975 * 𣏕 + ((꿱 + 999999976) * \
   (匳 + 999669526) + 𘬩) * 835609721 * (999999985 + 999999971 + 999990535 * (999998715 * \
   (u + 999999979) * ы + 999999678 + 975758218) + 837076177 * 682445949 + 𝖐 * 807995834 \
   * 嫓 * 999999982) * 15103324 * 999883091) + p + 997953345 + y + 999999995 + q * 쭕 * \
   (999999627 + 999995330)) * 999999836 * (999892519 + ǿ * (𔔏 + 994217472 + I * \
   999330058 * 758045348 + (늷 + 999990933) * 쇪 * 999523072 * 999999978 * 999963300 * ް + \
   999999148 + 纜) * u) * A * (𠇏 + 983841675) * (999999977 + (999999989 + w) * 684692078 \
   * (((999999975 + 966577944 * (999947774 * b * ș + 999994433 + Y) + o * 𧿒 + 999583315) \
   * ꫫ + 999999983) * (998338515 + 999999988 + 黎 + W * 999999982 * (999999873 + \
   999999935 + ﶏ) * (엣 + 999559553 + 練 * (995417962 * 198911502 + 999999942 + 998290735 \
   + 928080032 + (998308146 * l + ݑ * ((n + 999999968) * (999999973 + 296274699) + \
   999998740 * 999999852)) * (Ř + 999999975 * 999999974 * q + 넝) * 붿 * (ö + 뺭 * \
   878089517 * B * 959040043 * 燽)))) * 999999970 * (h + 999030056 + (999999986 + \
   999999431) * (v + (l + ʾ + D + ﰰ) * (999999955 * 䃦 * 댄 + 吤) + 999999941)) * 999973591 \
   * V * 999999990 * ҷ * メ + 999999980)) + 1000000000 "
;;

let expression_large_ascii =
  String.Utf8.map (String.Utf8.of_string_unchecked expression_large) ~f:(fun uchar ->
    match Uchar.to_char uchar with
    | None -> Uchar.of_char 'x'
    | Some _ -> uchar)
  |> String.Utf8.to_string
;;

let expression_large_bigstring = Bigstring.of_string expression_large
let expression_large_bigstring_ascii = Bigstring.of_string expression_large_ascii
let expression = "1 * 誫 + f + (g  (8 + 0 + 9) + 8 * 4) * 11 * 7 + 11 + i"
let expression_ascii = "1 * x + f + (g  (8 + 0 + 9) + 8 * 4) * 11 * 7 + 11 + i"
let%bench "uniparse_string" = parse_string parser expression ~consume:`All ~encoding:Utf8

let%bench "uniparse_string ascii" =
  parse_string parser expression_ascii ~consume:`All ~encoding:Utf8
;;

let%bench "uniparse_string large" =
  parse_string parser expression_large ~consume:`All ~encoding:Utf8
;;

let%bench "uniparse_string large ascii" =
  parse_string parser expression_large_ascii ~consume:`All ~encoding:Utf8
;;

let%bench "uniparse_bigstring large bigstring" =
  parse_bigstring parser expression_large_bigstring ~consume:`All ~encoding:Utf8
;;

let%bench "uniparse_bigstring large bigstring ascii" =
  parse_bigstring parser expression_large_bigstring_ascii ~consume:`All ~encoding:Utf8
;;

module Angstrom = struct
  open Angstrom
  open Let_syntax

  let parse_number =
    let%bind initial = satisfy Char.is_digit in
    scan_state (Char.get_digit_exn initial) (fun acc char ->
      let%map.Option digit = Char.get_digit char in
      (acc * 10) + digit)
  ;;

  let variable = satisfy Char.is_alpha
  let whitespace = skip_while Char.is_whitespace
  let open_parenthesis = satisfy (Char.equal '(')
  let close_parenthesis = satisfy (Char.equal ')')
  let add = satisfy (Char.equal '+')
  let mul = satisfy (Char.equal '*')

  let number_or_variable =
    choice [ parse_number >>| Ast.number; variable >>| Uchar.of_char >>| Ast.variable ]
  ;;

  let optional angstrom ~default ~return = option default (angstrom >>| return)

  let parser =
    fix (fun parser ->
      let multiplicative_unit =
        fix (fun multiplicative_unit ->
          let single_unit =
            whitespace
            *> choice
                 [ number_or_variable; open_parenthesis *> parser <* close_parenthesis ]
            <* whitespace
          in
          let%mapn left = single_unit
          and right =
            optional
              (optional mul ~default:() ~return:ignore *> multiplicative_unit)
              ~default:None
              ~return:Option.return
          in
          match right with
          | None -> left
          | Some right -> Ast.mul left right)
      in
      let%mapn left = multiplicative_unit
      and right = optional (add *> parser) ~default:None ~return:Option.return in
      match right with
      | None -> left
      | Some right -> Ast.add left right)
  ;;

  let%bench "parse_string" = parse_string parser expression_ascii ~consume:All
  let%bench "parse_string large" = parse_string parser expression_large_ascii ~consume:All

  let%bench "parse_bigstring large" =
    parse_bigstring parser expression_large_bigstring_ascii ~consume:All
  ;;
end
