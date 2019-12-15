(*<*) 
theory Glosario
  imports 
    Main 
    "HOL-Library.LaTeXsugar" 
    "HOL-Library.OptionalSugar"
    "HOL-Library.Countable"
begin
(*>*)

(* chapter \<open>Glosario de reglas\<close> *)

section \<open>Teoría de conjuntos finitos\<close>

text \<open>\comentario{Explicar la siguiente notación y recolocarla donde se
  use por primera vez.}\<close> 

text \<open>\comentario{Falta Corregir.}\<close> 

text \<open>A continuación se muestran resultamos relativos a la teoría 
  \href{https://n9.cl/x86r}{FiniteSet.thy}. Dicha teoría se basa en la definición recursiva de
  @{term "finite"}, que aparece retratada en la sección de \<open>Sintaxis\<close>. Además, hemos empleado los
  siguientes resultados. 

  \begin{itemize}
    \item[] @{thm[mode=Rule] finite_UnI[no_vars]} 
      \hfill (@{text finite_UnI})
  \end{itemize}\<close>

section \<open>Teoría de listas\<close>

text\<open>La teoría de listas en Isabelle corresponde a \href{http://bit.ly/2se9Oy0}{List.thy}. 
  Esta se fundamenta en la definición recursiva de @{term "list"}.\\

\<open>datatype (set': 'a) list' =\\
    Nil'  ("[]")\\
  | Cons' (hd: 'a) (tl: "'a list'")  (infixr "#" 65)\\
for\\
  map: map\\
  rel: list_all2\\
  pred: list_all\\
where\\
  "tl [] = []"\\\<close>

COMENTARIO: NO ME PERMITE PONERLO FUERA DEL ENTORNO DE TEXTO, NI CAMBIANDO EL NOMBRE \\

Como es habitual, hemos cambiado la notación de la definición a @{term "list'"} para no 
  definir dos veces de manera idéntica la misma noción. Simultáneamente se define la función
  de conjuntos @{term "set"} (idéntica a @{term "set'"}), una función @{term "map"}, una relación
  @{term "rel"} y un predicado @{term "pred"}. Para dicha definción hemos empleado los operadores
  sobre listas \<open>hd\<close> y \<open>tl\<close>.
  De este modo, \<open>hd\<close> aplicado a una lista de elementos de un tipo cualquiera \<open>'a\<close> nos 
  devuelve el primer elemento de la misma, y \<open>tl\<close>  nos 
  devuelve la lista quitando el primer elmento.
 
  Además, hemos utilizado las siguientes propiedades sobre listas.

  \begin{itemize}
    \item[] @{thm[mode=Rule] Un_insert_left[no_vars]} 
    \hfill (@{text Un_insert_left})
  \end{itemize}\<close>

section \<open>Teoría de conjuntos\<close>

text \<open>Los siguientes resultados empleados en el análisis hecho sobre la lógica proposicional 
  corresponden a la teoría de conjuntos de Isabelle: \href{https://n9.cl/qatp}{Set.thy}.

  \begin{itemize}
    \item[] @{thm[mode=Rule] set_append[no_vars]} 
      \hfill (@{text set_append})
    \item[] @{thm[mode=Rule] singletonI[no_vars]} 
      \hfill (@{text singletonI})
    \item[] @{thm[mode=Rule] insertI1[no_vars]} 
      \hfill (@{text insertI1})
    \item[] @{thm[mode=Rule] Un_empty_right[no_vars]} 
      \hfill (@{text Un_empty_right})
    \item[] @{thm[mode=Rule] subset_trans[no_vars]} 
      \hfill (@{text subset_trans})
    \item[] @{thm[mode=Rule] rev_subsetD[no_vars]} 
      \hfill (@{text rev_subsetD})
    \item[] @{thm[mode=Rule] Un_mono[no_vars]} 
      \hfill (@{text Un_mono})
    \item[] @{thm[mode=Rule] Un_upper1[no_vars]} 
      \hfill (@{text Un_upper1})
    \item[] @{thm[mode=Rule] Un_upper2[no_vars]} 
      \hfill (@{text Un_upper2})
    \item[] @{thm[mode=Rule] subset_refl[no_vars]} 
      \hfill (@{text subset_refl})
    \item[] @{thm[mode=Rule] empty_subsetI[no_vars]} 
      \hfill (@{text empty_subsetI})
    \item[] @{thm[mode=Rule] singletonD[no_vars]} 
      \hfill (@{text singletonD})
    \item[] @{thm[mode=Rule] Un_iff[no_vars]} 
      \hfill (@{text Un_iff})
  \end{itemize}
\<close>

section \<open>Lógica de primer orden\<close>

text \<open>En Isabelle corresponde a la teoría \href{http://bit.ly/38iFKlA}{HOL.thy}
  Los resultados empleados son los siguientes.

  \begin{itemize}
    \item[] @{thm[mode=Rule] conjunct1[no_vars]} 
      \hfill (@{text conjunct1})
    \item[] @{thm[mode=Rule] conjunct2[no_vars]} 
      \hfill (@{text conjunct2})
  \end{itemize}
\<close>

(*<*)
end
(*>*) 
