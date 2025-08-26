open! Core

(* Idea: add a run function that returns no result, to be used by
   consumed *)

module Encoding = struct
  type _ t =
    | Byte : [ `Byte ] t
    | Utf8 : [ `Unicode ] t
    | Utf16_be : [ `Unicode ] t
    | Utf16_le : [ `Unicode ] t
    | Utf32_be : [ `Unicode ] t
    | Utf32_le : [ `Unicode ] t
  [@@deriving sexp_of]

  type packed = Packed : _ t -> packed
end

module With_encoding = struct
  type ('a, 'encoding) t =
    { encoding : 'encoding Encoding.t
    ; value : 'a
    }

  let lift_string t ~(target_encoding : [ `Unicode ] Encoding.t) =
    let of_array array =
      match target_encoding with
      | Utf8 -> String.Utf8.of_array array |> String.Utf8.to_string
      | Utf16_be -> String.Utf16be.of_array array |> String.Utf16be.to_string
      | Utf16_le -> String.Utf16le.of_array array |> String.Utf16le.to_string
      | Utf32_be -> String.Utf32be.of_array array |> String.Utf32be.to_string
      | Utf32_le -> String.Utf32le.of_array array |> String.Utf32le.to_string
    in
    match t.encoding, target_encoding with
    | Utf8, Utf8
    | Utf16_be, Utf16_be
    | Utf16_le, Utf16_le
    | Utf32_be, Utf32_be
    | Utf32_le, Utf32_le -> t.value
    | Utf8, _ -> String.Utf8.of_string t.value |> String.Utf8.to_array |> of_array
    | Utf16_be, _ ->
      String.Utf16be.of_string t.value |> String.Utf16be.to_array |> of_array
    | Utf16_le, _ ->
      String.Utf16le.of_string t.value |> String.Utf16le.to_array |> of_array
    | Utf32_be, _ ->
      String.Utf32be.of_string t.value |> String.Utf32be.to_array |> of_array
    | Utf32_le, _ ->
      String.Utf32le.of_string t.value |> String.Utf32le.to_array |> of_array
  ;;
end

module Get_uchar = struct
  type ('base, _) t =
    | Get : ('base @ local -> int -> Uchar.Decode_result.t) -> ('base, [ `Unicode ]) t
    | Undef : ('base, [ `Byte ]) t
end

module Parse_result = struct
  type ('a : value_or_null) t =
    | Parsed of
        { value : 'a @@ global
        ; next_pos : int
        }
    | Failed of
        { reason : string @@ global
        ; call_pos : Source_code_position.t @@ global
        }
end

module Sub_target = struct
  type 'a t =
    | String : string t
    | Bytes : bytes t
    | Bigstring : Bigstring.t t
end

type ('base, 'target, 'enc) sub =
  'base @ local
  -> 'target Sub_target.t
  -> pos:int
  -> len:int
  -> ('target, 'enc) With_encoding.t

type ('a : value_or_null, 'char) t =
  { run :
      'base.
      'base @ local
      -> pos:int
      -> len:int
      -> unsafe_get_char:('base @ local -> int -> char) @ local
      -> unsafe_get_uchar:('base, 'char) Get_uchar.t @ local
      -> sub:('target. ('base, 'target, 'char) sub) @ local
      -> 'a Parse_result.t @ local
  }
[@@unboxed]

let fail ~(call_pos : [%call_pos]) reason =
  { run =
      (fun _base ~pos:_ ~len:_ ~unsafe_get_char:_ ~unsafe_get_uchar:_ ~sub:_ ->
        Failed { reason; call_pos })
  }
;;

let return value =
  { run =
      (fun _base ~pos ~len:_ ~unsafe_get_char:_ ~unsafe_get_uchar:_ ~sub:_ ->
        Parsed { value; next_pos = pos })
  }
;;

let bind t ~f =
  { run =
      (fun base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->
        match t.run base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value; next_pos } ->
          let next = f value in
          exclave_
          next.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub
        | Failed { reason; call_pos } -> Failed { reason; call_pos })
  }
;;

let map t ~f =
  { run =
      (fun base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->
        match t.run base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value; next_pos } -> Parsed { value = f value; next_pos }
        | Failed { reason; call_pos } -> Failed { reason; call_pos })
  }
;;

let map = `Custom map

include functor Monad.Make2

let both t1 t2 =
  { run =
      (fun base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->
        match t1.run base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value = v1; next_pos } ->
          (match
             t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub
           with
           | Parsed { value = v2; next_pos } ->
             exclave_ Parsed { value = v1, v2; next_pos }
           | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
        | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
  }
;;

module Nary_monadic_operators = struct
  (*$
    open! Core

    (* dune doesn't support setting the formatter yet, so we have to
       do this ugly trick. *)
    let () = print_endline ""
    let () = print_endline {|  [@@@ocamlformat "disable"]|}
    let () = print_endline ""

    let make_run n ~content =
      [%string
        {| (match t%{n#Int}.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v%{n#Int}; next_pos } ->
          %{content}
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })|}]
    ;;

    let make_t ~content =
      [%string
        {| { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub -> %{content}) }|}]
    ;;

    let make_function n ~name ~content =
      let arguments =
        List.init n ~f:(fun i -> [%string {|t%{i#Int}|}]) |> String.concat ~sep:" "
      in
      let f_arguments =
        List.init n ~f:(fun i -> [%string {|v%{i#Int}|}]) |> String.concat ~sep:" "
      in
      let content = content ~arguments:f_arguments in
      let content =
        Sequence.range ~stride:(-1) ~start:`exclusive ~stop:`inclusive n 0
        |> Sequence.fold ~init:content ~f:(fun content i -> make_run i ~content)
      in
      let content = make_t ~content in
      [%string {|  let %{name}%{n#Int} %{arguments} ~f = %{content}|}]
      ^ "\n"
    ;;

    let () =
      for i = 2 to 16 do
        make_function i ~name:"map" ~content:(fun ~arguments ->
          [%string "exclave_ Parsed { value = f %{arguments}; next_pos }"])
        |> print_endline
      done
    ;;

    let () =
      for i = 2 to 16 do
        make_function i ~name:"bind" ~content:(fun ~arguments ->
          [%string
            {|
        (match (f %{arguments}).run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value; next_pos } -> exclave_ Parsed { value; next_pos }
        | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })|}])
        |> print_endline
      done;;
    
    let () = print_string "  "
  *)
  [@@@ocamlformat "disable"]

  let map2 t0 t1 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
          exclave_ Parsed { value = f v0 v1; next_pos }
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let map3 t0 t1 t2 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
          exclave_ Parsed { value = f v0 v1 v2; next_pos }
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let map4 t0 t1 t2 t3 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
          exclave_ Parsed { value = f v0 v1 v2 v3; next_pos }
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let map5 t0 t1 t2 t3 t4 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
          exclave_ Parsed { value = f v0 v1 v2 v3 v4; next_pos }
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let map6 t0 t1 t2 t3 t4 t5 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
           (match t5.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v5; next_pos } ->
          exclave_ Parsed { value = f v0 v1 v2 v3 v4 v5; next_pos }
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let map7 t0 t1 t2 t3 t4 t5 t6 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
           (match t5.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v5; next_pos } ->
           (match t6.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v6; next_pos } ->
          exclave_ Parsed { value = f v0 v1 v2 v3 v4 v5 v6; next_pos }
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let map8 t0 t1 t2 t3 t4 t5 t6 t7 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
           (match t5.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v5; next_pos } ->
           (match t6.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v6; next_pos } ->
           (match t7.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v7; next_pos } ->
          exclave_ Parsed { value = f v0 v1 v2 v3 v4 v5 v6 v7; next_pos }
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let map9 t0 t1 t2 t3 t4 t5 t6 t7 t8 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
           (match t5.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v5; next_pos } ->
           (match t6.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v6; next_pos } ->
           (match t7.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v7; next_pos } ->
           (match t8.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v8; next_pos } ->
          exclave_ Parsed { value = f v0 v1 v2 v3 v4 v5 v6 v7 v8; next_pos }
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let map10 t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
           (match t5.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v5; next_pos } ->
           (match t6.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v6; next_pos } ->
           (match t7.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v7; next_pos } ->
           (match t8.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v8; next_pos } ->
           (match t9.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v9; next_pos } ->
          exclave_ Parsed { value = f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9; next_pos }
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let map11 t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
           (match t5.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v5; next_pos } ->
           (match t6.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v6; next_pos } ->
           (match t7.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v7; next_pos } ->
           (match t8.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v8; next_pos } ->
           (match t9.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v9; next_pos } ->
           (match t10.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v10; next_pos } ->
          exclave_ Parsed { value = f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10; next_pos }
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let map12 t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
           (match t5.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v5; next_pos } ->
           (match t6.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v6; next_pos } ->
           (match t7.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v7; next_pos } ->
           (match t8.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v8; next_pos } ->
           (match t9.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v9; next_pos } ->
           (match t10.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v10; next_pos } ->
           (match t11.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v11; next_pos } ->
          exclave_ Parsed { value = f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11; next_pos }
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let map13 t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
           (match t5.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v5; next_pos } ->
           (match t6.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v6; next_pos } ->
           (match t7.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v7; next_pos } ->
           (match t8.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v8; next_pos } ->
           (match t9.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v9; next_pos } ->
           (match t10.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v10; next_pos } ->
           (match t11.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v11; next_pos } ->
           (match t12.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v12; next_pos } ->
          exclave_ Parsed { value = f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12; next_pos }
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let map14 t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
           (match t5.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v5; next_pos } ->
           (match t6.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v6; next_pos } ->
           (match t7.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v7; next_pos } ->
           (match t8.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v8; next_pos } ->
           (match t9.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v9; next_pos } ->
           (match t10.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v10; next_pos } ->
           (match t11.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v11; next_pos } ->
           (match t12.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v12; next_pos } ->
           (match t13.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v13; next_pos } ->
          exclave_ Parsed { value = f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13; next_pos }
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let map15 t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
           (match t5.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v5; next_pos } ->
           (match t6.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v6; next_pos } ->
           (match t7.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v7; next_pos } ->
           (match t8.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v8; next_pos } ->
           (match t9.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v9; next_pos } ->
           (match t10.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v10; next_pos } ->
           (match t11.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v11; next_pos } ->
           (match t12.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v12; next_pos } ->
           (match t13.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v13; next_pos } ->
           (match t14.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v14; next_pos } ->
          exclave_ Parsed { value = f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14; next_pos }
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let map16 t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
           (match t5.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v5; next_pos } ->
           (match t6.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v6; next_pos } ->
           (match t7.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v7; next_pos } ->
           (match t8.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v8; next_pos } ->
           (match t9.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v9; next_pos } ->
           (match t10.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v10; next_pos } ->
           (match t11.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v11; next_pos } ->
           (match t12.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v12; next_pos } ->
           (match t13.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v13; next_pos } ->
           (match t14.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v14; next_pos } ->
           (match t15.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v15; next_pos } ->
          exclave_ Parsed { value = f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15; next_pos }
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let bind2 t0 t1 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
          
        (match (f v0 v1).run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value; next_pos } -> exclave_ Parsed { value; next_pos }
        | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let bind3 t0 t1 t2 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
          
        (match (f v0 v1 v2).run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value; next_pos } -> exclave_ Parsed { value; next_pos }
        | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let bind4 t0 t1 t2 t3 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
          
        (match (f v0 v1 v2 v3).run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value; next_pos } -> exclave_ Parsed { value; next_pos }
        | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let bind5 t0 t1 t2 t3 t4 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
          
        (match (f v0 v1 v2 v3 v4).run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value; next_pos } -> exclave_ Parsed { value; next_pos }
        | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let bind6 t0 t1 t2 t3 t4 t5 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
           (match t5.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v5; next_pos } ->
          
        (match (f v0 v1 v2 v3 v4 v5).run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value; next_pos } -> exclave_ Parsed { value; next_pos }
        | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let bind7 t0 t1 t2 t3 t4 t5 t6 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
           (match t5.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v5; next_pos } ->
           (match t6.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v6; next_pos } ->
          
        (match (f v0 v1 v2 v3 v4 v5 v6).run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value; next_pos } -> exclave_ Parsed { value; next_pos }
        | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let bind8 t0 t1 t2 t3 t4 t5 t6 t7 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
           (match t5.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v5; next_pos } ->
           (match t6.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v6; next_pos } ->
           (match t7.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v7; next_pos } ->
          
        (match (f v0 v1 v2 v3 v4 v5 v6 v7).run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value; next_pos } -> exclave_ Parsed { value; next_pos }
        | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let bind9 t0 t1 t2 t3 t4 t5 t6 t7 t8 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
           (match t5.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v5; next_pos } ->
           (match t6.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v6; next_pos } ->
           (match t7.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v7; next_pos } ->
           (match t8.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v8; next_pos } ->
          
        (match (f v0 v1 v2 v3 v4 v5 v6 v7 v8).run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value; next_pos } -> exclave_ Parsed { value; next_pos }
        | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let bind10 t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
           (match t5.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v5; next_pos } ->
           (match t6.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v6; next_pos } ->
           (match t7.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v7; next_pos } ->
           (match t8.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v8; next_pos } ->
           (match t9.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v9; next_pos } ->
          
        (match (f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9).run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value; next_pos } -> exclave_ Parsed { value; next_pos }
        | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let bind11 t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
           (match t5.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v5; next_pos } ->
           (match t6.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v6; next_pos } ->
           (match t7.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v7; next_pos } ->
           (match t8.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v8; next_pos } ->
           (match t9.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v9; next_pos } ->
           (match t10.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v10; next_pos } ->
          
        (match (f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10).run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value; next_pos } -> exclave_ Parsed { value; next_pos }
        | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let bind12 t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
           (match t5.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v5; next_pos } ->
           (match t6.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v6; next_pos } ->
           (match t7.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v7; next_pos } ->
           (match t8.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v8; next_pos } ->
           (match t9.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v9; next_pos } ->
           (match t10.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v10; next_pos } ->
           (match t11.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v11; next_pos } ->
          
        (match (f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11).run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value; next_pos } -> exclave_ Parsed { value; next_pos }
        | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let bind13 t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
           (match t5.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v5; next_pos } ->
           (match t6.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v6; next_pos } ->
           (match t7.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v7; next_pos } ->
           (match t8.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v8; next_pos } ->
           (match t9.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v9; next_pos } ->
           (match t10.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v10; next_pos } ->
           (match t11.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v11; next_pos } ->
           (match t12.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v12; next_pos } ->
          
        (match (f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12).run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value; next_pos } -> exclave_ Parsed { value; next_pos }
        | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let bind14 t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
           (match t5.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v5; next_pos } ->
           (match t6.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v6; next_pos } ->
           (match t7.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v7; next_pos } ->
           (match t8.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v8; next_pos } ->
           (match t9.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v9; next_pos } ->
           (match t10.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v10; next_pos } ->
           (match t11.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v11; next_pos } ->
           (match t12.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v12; next_pos } ->
           (match t13.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v13; next_pos } ->
          
        (match (f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13).run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value; next_pos } -> exclave_ Parsed { value; next_pos }
        | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let bind15 t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
           (match t5.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v5; next_pos } ->
           (match t6.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v6; next_pos } ->
           (match t7.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v7; next_pos } ->
           (match t8.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v8; next_pos } ->
           (match t9.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v9; next_pos } ->
           (match t10.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v10; next_pos } ->
           (match t11.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v11; next_pos } ->
           (match t12.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v12; next_pos } ->
           (match t13.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v13; next_pos } ->
           (match t14.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v14; next_pos } ->
          
        (match (f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14).run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value; next_pos } -> exclave_ Parsed { value; next_pos }
        | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  let bind16 t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15 ~f =  { run = (fun base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->  (match t0.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v0; next_pos } ->
           (match t1.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v1; next_pos } ->
           (match t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v2; next_pos } ->
           (match t3.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v3; next_pos } ->
           (match t4.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v4; next_pos } ->
           (match t5.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v5; next_pos } ->
           (match t6.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v6; next_pos } ->
           (match t7.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v7; next_pos } ->
           (match t8.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v8; next_pos } ->
           (match t9.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v9; next_pos } ->
           (match t10.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v10; next_pos } ->
           (match t11.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v11; next_pos } ->
           (match t12.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v12; next_pos } ->
           (match t13.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v13; next_pos } ->
           (match t14.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v14; next_pos } ->
           (match t15.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
      | Parsed { value = v15; next_pos } ->
          
        (match (f v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15).run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value; next_pos } -> exclave_ Parsed { value; next_pos }
        | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
      | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })) }

  (*$*)

  [@@@ocamlformat "enable"]
end

include Nary_monadic_operators

module Let_syntax = struct
  include Let_syntax

  module Let_syntax = struct
    open struct
      let both_ = both
    end

    include Let_syntax

    let both = both_

    include Nary_monadic_operators
  end
end

let satisfy_ascii ~(call_pos : [%call_pos]) f =
  { run =
      (fun base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar:_ ~sub:_ -> exclave_
        if pos < len
        then (
          let char = unsafe_get_char base pos in
          if f char
          then Parsed { value = char; next_pos = pos + 1 }
          else Failed { reason = "satisfy"; call_pos })
        else Failed { reason = "satisfy reached end"; call_pos })
  }
;;

let satisfy ~(call_pos : [%call_pos]) f =
  { run =
      (fun base
        ~pos
        ~len
        ~unsafe_get_char:_
        ~unsafe_get_uchar:(Get unsafe_get_uchar)
        ~sub:_ -> exclave_
        if pos < len
        then (
          let uchar = unsafe_get_uchar base pos in
          let value = Uchar.Decode_result.uchar_or_replacement_char uchar in
          if f value
          then Parsed { value; next_pos = pos + Uchar.Decode_result.bytes_consumed uchar }
          else Failed { reason = "usatisfy"; call_pos })
        else Failed { reason = "usatisfy reached end"; call_pos })
  }
;;

let rec loop_choices
  ~call_pos
  ~failure_message
  choices
  base
  ~pos
  ~len
  ~unsafe_get_char
  ~unsafe_get_uchar
  ~(sub : 'target. ('base, 'target, _) sub)
  : _ Parse_result.t @ local
  =
  match choices with
  | [] -> exclave_ Failed { reason = failure_message; call_pos }
  | choice :: choices ->
    (match choice.run base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
     | Parsed { value; next_pos } -> exclave_ Parsed { value; next_pos }
     | Failed _ ->
       exclave_
       loop_choices
         ~call_pos
         ~failure_message
         choices
         base
         ~pos
         ~len
         ~unsafe_get_char
         ~unsafe_get_uchar
         ~sub)
;;

let choose ~(call_pos : [%call_pos]) ?(failure_message = "choose") choices =
  { run =
      (fun base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub -> exclave_
        loop_choices
          ~call_pos
          ~failure_message
          choices
          base
          ~pos
          ~len
          ~unsafe_get_char
          ~unsafe_get_uchar
          ~sub)
  }
;;

let skip_bytes ~(call_pos : [%call_pos]) ?(on_overflow = `Fail "skip_bytes overflow") n =
  { run =
      (fun _base ~pos ~len ~unsafe_get_char:_ ~unsafe_get_uchar:_ ~sub:_ -> exclave_
        let next_pos = pos + n in
        if next_pos > len
        then (
          match on_overflow with
          | `Fail reason -> Failed { reason; call_pos }
          | `Truncate -> Parsed { value = (); next_pos = len })
        else Parsed { value = (); next_pos })
  }
;;

let skip_chars ~(call_pos : [%call_pos]) ?(on_overflow = `Fail "skip_chars overflow") n =
  { run =
      (fun base
        ~pos
        ~len
        ~unsafe_get_char:_
        ~unsafe_get_uchar:(Get unsafe_get_uchar)
        ~sub:_ ->
        let rec loop base n ~pos ~len ~unsafe_get_uchar : _ Parse_result.t @ local =
          if n = 0
          then exclave_ Parsed { value = (); next_pos = pos }
          else if pos < len
          then (
            let uchar = unsafe_get_uchar base pos in
            exclave_
            loop
              base
              (n - 1)
              ~pos:(pos + Uchar.Decode_result.bytes_consumed uchar)
              ~len
              ~unsafe_get_uchar)
          else (
            match on_overflow with
            | `Fail reason -> exclave_ Failed { reason; call_pos }
            | `Truncate -> exclave_ Parsed { value = (); next_pos = len })
        in
        exclave_ loop base n ~pos ~len ~unsafe_get_uchar)
  }
;;

let skip_while_ascii f =
  { run =
      (fun base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar:_ ~sub:_ ->
        let rec loop base ~pos ~len ~unsafe_get_char : _ Parse_result.t @ local =
          if pos < len
          then (
            let char = unsafe_get_char base pos in
            if f char
            then exclave_ loop base ~pos:(pos + 1) ~len ~unsafe_get_char
            else exclave_ Parsed { value = (); next_pos = pos })
          else exclave_ Parsed { value = (); next_pos = pos }
        in
        exclave_ loop base ~pos ~len ~unsafe_get_char)
  }
;;

let skip_while f =
  { run =
      (fun base
        ~pos
        ~len
        ~unsafe_get_char:_
        ~unsafe_get_uchar:(Get unsafe_get_uchar)
        ~sub:_ ->
        let rec loop base ~pos ~len ~unsafe_get_uchar : _ Parse_result.t @ local =
          if pos < len
          then (
            let uchar = unsafe_get_uchar base pos in
            if f (Uchar.Decode_result.uchar_or_replacement_char uchar)
            then
              exclave_
              loop
                base
                ~pos:(pos + Uchar.Decode_result.bytes_consumed uchar)
                ~len
                ~unsafe_get_uchar
            else exclave_ Parsed { value = (); next_pos = pos })
          else exclave_ Parsed { value = (); next_pos = pos }
        in
        exclave_ loop base ~pos ~len ~unsafe_get_uchar)
  }
;;

let fold_while ~f ~init =
  { run =
      (fun base
        ~pos
        ~len
        ~unsafe_get_char:_
        ~unsafe_get_uchar:(Get unsafe_get_uchar)
        ~sub:_ ->
        let rec loop base ~pos ~len ~unsafe_get_uchar ~init : _ Parse_result.t @ local =
          if pos < len
          then (
            let uchar = unsafe_get_uchar base pos in
            match f init (Uchar.Decode_result.uchar_or_replacement_char uchar) with
            | This init ->
              exclave_
              loop
                base
                ~pos:(pos + Uchar.Decode_result.bytes_consumed uchar)
                ~len
                ~unsafe_get_uchar
                ~init
            | Null -> exclave_ Parsed { value = init; next_pos = pos })
          else exclave_ Parsed { value = init; next_pos = pos }
        in
        exclave_ loop base ~pos ~len ~unsafe_get_uchar ~init)
  }
;;

let nonempty ~(call_pos : [%call_pos]) t =
  { run =
      (fun base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->
        match t.run base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value; next_pos } ->
          if next_pos > pos
          then exclave_ Parsed { value; next_pos }
          else exclave_ Failed { reason = "nonempty"; call_pos }
        | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
  }
;;

let consumed' t ~target =
  { run =
      (fun base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->
        match t.run base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value = _; next_pos } ->
          exclave_ Parsed { value = sub base target ~pos ~len:(next_pos - pos); next_pos }
        | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
  }
;;

let consumed t = consumed' t ~target:String

let fix f =
  let rec t =
    { run =
        (fun base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub -> exclave_
          (f t).run base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub)
    }
  in
  t
;;

let end_of_input ~(call_pos : [%call_pos]) () =
  { run =
      (fun _base ~pos ~len ~unsafe_get_char:_ ~unsafe_get_uchar:_ ~sub:_ ->
        if pos = len
        then exclave_ Parsed { value = (); next_pos = pos }
        else exclave_ Failed { reason = "end_of_input"; call_pos })
  }
;;

let string ~(call_pos : [%call_pos]) s =
  { run =
      (fun base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar:_ ~sub:_ ->
        let string_len = String.length s in
        if len < pos + string_len
        then exclave_ Failed { reason = "string"; call_pos }
        else (
          let rec equal i =
            if i = string_len
            then true
            else if Char.equal (String.unsafe_get s i) (unsafe_get_char base (pos + i))
            then equal (i + 1)
            else false
          in
          if equal 0
          then exclave_ Parsed { value = s; next_pos = pos + string_len }
          else exclave_ Failed { reason = "string"; call_pos }))
  }
;;

let optional (type a : value_or_null) t ~(default : a) ~return =
  { run =
      (fun base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->
        match t.run base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value; next_pos } -> exclave_ Parsed { value = return value; next_pos }
        | Failed _ -> exclave_ Parsed { value = default; next_pos = pos })
  }
;;

let ( <* ) t1 t2 =
  { run =
      (fun base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->
        match t1.run base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value; next_pos } ->
          (match
             t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub
           with
           | Parsed { value = _; next_pos } -> exclave_ Parsed { value; next_pos }
           | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
        | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
  }
;;

let ( *> ) t1 t2 =
  { run =
      (fun base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub ->
        match t1.run base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
        | Parsed { value = _; next_pos } ->
          (match
             t2.run base ~pos:next_pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub
           with
           | Parsed { value; next_pos } -> exclave_ Parsed { value; next_pos }
           | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
        | Failed { reason; call_pos } -> exclave_ Failed { reason; call_pos })
  }
;;

let parse_generic
  ~(call_pos : [%call_pos])
  t
  base
  ~pos
  ~len
  ~consume
  ~unsafe_get_char
  ~unsafe_get_uchar
  ~(sub : 'target. ('base, 'target, _) sub)
  =
  match t.run base ~pos ~len ~unsafe_get_char ~unsafe_get_uchar ~sub with
  | Parsed { value; next_pos } ->
    (match next_pos < len, consume with
     | _, `Prefix | false, `All -> Ok value
     | true, `All ->
       error_s
         [%message
           "Parse error, consume is `All but not all of the input was consumed"
             (call_pos : Source_code_position.t)])
  | Failed { reason; call_pos } ->
    error_s [%message reason (call_pos : Source_code_position.t)]
;;

let parse_string
  (type encoding)
  ~(call_pos : [%call_pos])
  t
  ?(pos = 0)
  ?len
  s
  ~consume
  ~(encoding : encoding Encoding.t)
  =
  let string_len = String.length s in
  let len =
    match len with
    | None -> string_len
    | Some len -> if len > string_len then string_len else len
  in
  let unsafe_get_uchar : (string, encoding) Get_uchar.t =
    match encoding with
    | Byte -> Get_uchar.Undef
    | Utf8 -> Get_uchar.Get (fun s byte_pos -> String.Utf8.get_unchecked s ~byte_pos)
    | Utf16_be ->
      Get_uchar.Get (fun s byte_pos -> String.Utf16be.get_unchecked s ~byte_pos)
    | Utf16_le ->
      Get_uchar.Get (fun s byte_pos -> String.Utf16le.get_unchecked s ~byte_pos)
    | Utf32_be ->
      Get_uchar.Get (fun s byte_pos -> String.Utf32be.get_unchecked s ~byte_pos)
    | Utf32_le ->
      Get_uchar.Get (fun s byte_pos -> String.Utf32le.get_unchecked s ~byte_pos)
  in
  let sub (type target) (base : string @ local) (target : target Sub_target.t) ~pos ~len =
    let value : target =
      match target with
      | String ->
        Bytes.unsafe_to_string
          ~no_mutation_while_string_reachable:(Bytes.From_string.sub base ~pos ~len)
      | Bytes -> Bytes.From_string.sub base ~pos ~len
      | Bigstring -> Bigstring.From_string.sub base ~pos ~len
    in
    { With_encoding.encoding; value }
  in
  parse_generic
    ~call_pos
    t
    s
    ~pos
    ~len
    ~consume
    ~unsafe_get_char:String.unsafe_get
    ~unsafe_get_uchar
    ~sub
;;

module Test = struct
  open! Let_syntax

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

  let number_or_variable =
    choose [ parse_number >>| Ast.number; variable >>| Ast.variable ]
  ;;

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
    " (862443739 * 981384025 + 991989189) * (999899699 * ((H + (999999981 + c + \
     (999958028 + 999328371) * ((999980997 * j * (632026619 + 999999841 + 999999350 * (Ķ \
     + i * G)) * 999999789 * ġ + ߊ + (999999967 + 999999720) * Μ + 999996565) * 쩍 + (һ * \
     (888152593 + 4687481 * 999642068 * ڗ * (r + (㑒 + 999998436 * b * 999992099 * (J * \
     (999999841 + 䄮) * (157526090 + (999999785 * 999954712 + 敵 * A * (c * 999996271 * F \
     + 999887728 + س * (999442988 * 998353295 * (ү + (999241744 + 999991856) * ެ) * \
     894762185 * ᓕ + 999999899 + 𮶢 + (799312578 * Γ + 154035502 * 999999942 * 999476517 \
     * (999999861 + 999987882) * ص * (997862169 + 멞 + 999999918 + 999999461 + 999985101 \
     + M) * 999999931 * 985154871 * Ἷ) * (885313214 * (ﳘ + 뵶 * ﺚ * ꠒ * (999999942 * \
     (999992433 + x * (999999312 + 999985384 + 뜒)) + 999999943)) * 999979299 + H + s + J \
     * (484668101 + Y * A) * (999999942 + 999999919) * (R + 996316176)) * (998196871 * Y \
     + 𘗆 + 𥸯) * h * B) * n * ʮ + 45379621)) * (秱 + (s * 908969893 * (y + 蚴) * 999999490 \
     + 999999757) * (y * 999997655 * (Ꙟ * (900137628 + Φ) + 999965013 + C + N + o) * \
     999998606 * (㡉 * (999999824 * 999972744 + 996630387 + o) + 852349872 + 999997941 * \
     999882311) + ((ﺕ + 743653466 * ﰋ + y) * 996603931 + 彫 + 𗸩) * 999999327) * 845627049 \
     * Q * 999999713 * Ķ) + O + 룔) + 897722322 * 931550842) * C * (พ * 999995615 + \
     999999865)) * (p + R * E)) * (腤 * 999999972 + 999921654 * (892067839 + K + q + V))) \
     + (瓘 + 996400942 * (ᧅ + 999999969 + (999999769 + E + ࢗ) * 999999870 * 999999897 + \
     944194501 + 993626226 + 999871527) * (B + ﹽ)) * l * 317146659 + 999987902) * 슧 * \
     (989442926 + d)) * 999878574 * ((999983662 + 炋 * 999999970 * (998310488 + N + \
     999999966 * п) * 999089674 * ɻ + 穖 + 999931977 * 999999675 + Ӣ + 999825654 * (p * \
     999999855 * (f + e) * 999791996 + D) + 덏 + 750485980) * 꾪 + ȋ * j * Ȱ) * 999910002 \
     * E * 999999689 * 999727624) * (ۺ + 濾 * 跐 + (999999589 * 999998575 + ϊ) * \
     881638576) + u) * ꦮ * 999966188 * (((999999980 + 999999906 + 999838575 * j) * \
     999990744 + 999995135 + ((Z * ȕ * ((999999974 + ٯ * 999999115) * (774170422 * \
     193559086 + 맫) + 칡) * 㚘 + 999999978) * (999680285 + P + (U + ꑕ * (o * 吔 + 柮) * 𠊼) * \
     (밤 + ß + 999999484) * 702410807) + 999862719 + b * 𪯚 + 999995862 + ح) * (댧 + f)) * \
     999874096 + U) * e + 999999975 * 𣏕 + ((꿱 + 999999976) * (匳 + 999669526) + 𘬩) * \
     835609721 * (999999985 + 999999971 + 999990535 * (999998715 * (u + 999999979) * ы + \
     999999678 + 975758218) + 837076177 * 682445949 + 𝖐 * 807995834 * 嫓 * 999999982) * \
     15103324 * 999883091) + p + 997953345 + y + 999999995 + q * 쭕 * (999999627 + \
     999995330)) * 999999836 * (999892519 + ǿ * (𔔏 + 994217472 + I * 999330058 * \
     758045348 + (늷 + 999990933) * 쇪 * 999523072 * 999999978 * 999963300 * ް + 999999148 \
     + 纜) * u) * A * (𠇏 + 983841675) * (999999977 + (999999989 + w) * 684692078 * \
     (((999999975 + 966577944 * (999947774 * b * ș + 999994433 + Y) + o * 𧿒 + 999583315) \
     * ꫫ + 999999983) * (998338515 + 999999988 + 黎 + W * 999999982 * (999999873 + \
     999999935 + ﶏ) * (엣 + 999559553 + 練 * (995417962 * 198911502 + 999999942 + \
     998290735 + 928080032 + (998308146 * l + ݑ * ((n + 999999968) * (999999973 + \
     296274699) + 999998740 * 999999852)) * (Ř + 999999975 * 999999974 * q + 넝) * 붿 * (ö \
     + 뺭 * 878089517 * B * 959040043 * 燽)))) * 999999970 * (h + 999030056 + (999999986 + \
     999999431) * (v + (l + ʾ + D + ﰰ) * (999999955 * 䃦 * 댄 + 吤) + 999999941)) * \
     999973591 * V * 999999990 * ҷ * メ + 999999980)) + 1000000000 "
  ;;

  let expression_large_ascii =
    String.Utf8.map (String.Utf8.of_string_unchecked expression_large) ~f:(fun uchar ->
      match Uchar.to_char uchar with
      | None -> Uchar.of_char 'x'
      | Some _ -> uchar)
    |> String.Utf8.to_string
  ;;

  let expression = "1 * 誫 + f + (g  (8 + 0 + 9) + 8 * 4) * 11 * 7 + 11 + i"
  let expression_ascii = "1 * x + f + (g  (8 + 0 + 9) + 8 * 4) * 11 * 7 + 11 + i"

  let%bench "uniparse_string" =
    parse_string parser expression ~consume:`All ~encoding:Utf8
  ;;

  let%bench "uniparse_string ascii" =
    parse_string parser expression_ascii ~consume:`All ~encoding:Utf8
  ;;

  let%bench "uniparse_string large" =
    parse_string parser expression_large ~consume:`All ~encoding:Utf8
  ;;

  let%bench "uniparse_string large ascii" =
    parse_string parser expression_large_ascii ~consume:`All ~encoding:Utf8
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

    let%bench "parse_string large" =
      parse_string parser expression_large_ascii ~consume:All
    ;;
  end
end
