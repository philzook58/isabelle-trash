theory MyTheory
imports Complex_Main (* Main https://isabelle.in.tum.de/library/HOL/HOL/Main.html *)
begin
(* https://isabelle.in.tum.de/dist/Isabelle2019/doc/main.pdf *)
datatype mytype = Here | There

fun flippo :: "mytype \<Rightarrow> mytype" where
"flippo Here = There" |
"flippo There = Here"

lemma flipflop [simp] : "flippo (flippo x) = x"
  apply(induction)
  apply(auto)
done

text "markup you can write stuff"



lemma add_comm : "(x :: nat) + y = y + x"
  apply(auto)
  done

value "(1 :: nat) + 1"
value "(1 :: real) + 1"

type_synonym foo = "mytype"

value "[ 1 , 2 , 3 ] :: nat list"
value "True :: bool"
value "True | False"
value "True & False"
value "~ True"
value "fst (True,False)"
value "Some True :: bool option"
value "None :: nat option"
value "if True then 1 else 2 :: nat"
value "append [x,y] [z]"
value "Nil :: nat list"
value "hd [True,False]"
value "tl [True,False]"
value "length []"
value "Suc 0"
value "[1 .. 10]"
value "[2 * x . x <- [1 .. 10] ]"
value "(1 :: nat) \<le> 10"
value "() :: unit" (* https://isabelle.in.tum.de/dist/library/HOL/HOL/Product_Type.html *)
value "\<lambda> x. Suc x" (* lmabda functions *)
value "%x. Suc x"
value "(%x. Suc x) 3"
value "{} :: unit set" (* sets *)
value "{1,2,3,4} :: nat set"
value "real 3"
value "sum {1 .. (10 :: nat)}"


(* value "fn x  x"
value "{e . LAM e. e \<le> 10 }"
*)

(* \<forall> *)

(* Lists https://isabelle.in.tum.de/dist/library/HOL/HOL/List.html  *)
(*   *)
fun sumn :: "nat \<Rightarrow> nat" where
"sumn (Suc n) = (Suc n) + (sumn n)" |
"sumn 0 = 0"

lemma summer : "2 * (sumn n) = (n + 1) * n"
  apply(induction n)
  apply(auto)
  done
  


fun mynot :: "bool \<Rightarrow> bool" where
"mynot b = b" 

lemma add_comm : "x + y = y + x"




end