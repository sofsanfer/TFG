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

text \<open>En este glosario se recoge la lista de los lemas usados en
  indicando la página del \href{http://bit.ly/2OMbjMM}{libro de HOL} 
  donde se encuentran.\<close>

section \<open>Teoría de conjuntos (7)\<close>

text \<open>Los siguientes resultados corresponden a la teoría de conjuntos 
  \href{https://n9.cl/qatp}{Set.thy}.\<close>

subsection \<open>Operaciones básicas (7.3)\<close>

subsubsection \<open>Subconjuntos (7.3.1)\<close>

text \<open>
  \begin{itemize}
    \item (p.165) @{thm[mode=Rule] rev_subsetD[no_vars]} 
      \hfill (@{text rev_subsetD})
    \item (p.166) @{thm[mode=Rule] subset_refl[no_vars]} 
      \hfill (@{text subset_refl})
    \item (p.166) @{thm[mode=Rule] subset_trans[no_vars]} 
      \hfill (@{text subset_trans})
  \end{itemize}\<close>

subsubsection \<open>El conjunto vacío (7.3.3)\<close>

text \<open>
  \begin{itemize}
    \item (p.167) @{thm[mode=Rule] empty_subsetI[no_vars]} 
      \hfill (@{text empty_subsetI})
  \end{itemize}\<close>

subsubsection \<open>Unión binaria (7.3.8)\<close>

text \<open>
  \begin{itemize}
    \item (p.169) @{thm[mode=Rule] Un_iff[no_vars]} 
      \hfill (@{text Un_iff})
    \item (p.169) @{thm[mode=Rule] UnI1[no_vars]} 
      \hfill (@{text UnI1})
    \item (p.170) @{thm[mode=Rule] UnI2[no_vars]} 
      \hfill (@{text UnI2})
\<close>

subsubsection \<open>Aumentar un conjunto - insertar (7.3.10)\<close>

text \<open>
  \begin{itemize}
    \item (p.171) @{thm[mode=Rule] set_insert[no_vars]} 
      \hfill (@{text set_insert})
  \end{itemize}\<close>

subsubsection \<open>Conjuntos unitarios, insertar (7.3.11)\<close>

text\<open>
  \begin{itemize}
    \item (p.172) @{thm[mode=Rule] singletonI[no_vars]} 
      \hfill (@{text singletonI})
    \item (p.172) @{thm[mode=Rule] singletonD[no_vars]} 
      \hfill (@{text singletonD})
  \end{itemize}
\<close>

subsubsection \<open>Reglas derivadas sobre subconjuntos (7.4.2)\<close>

text \<open>
  \begin{itemize}
    \item (p.177) @{thm[mode=Rule] Un_upper1[no_vars]} 
      \hfill (@{text Un_upper1})
    \item (p.177) @{thm[mode=Rule] Un_upper2[no_vars]} 
      \hfill (@{text Un_upper2})
  \end{itemize}\<close>

subsubsection \<open>Igualdades sobre la union, intersección, inclusion, 
  etc. (7.4.3)\<close>

text \<open>
  \begin{itemize}
    \item (p.181) @{thm[mode=Rule] Un_absorb[no_vars]} 
      \hfill (@{text Un_absorb})
    \item (p.181) @{thm[mode=Rule] Un_empty_right[no_vars]} 
      \hfill (@{text Un_empty_right})
    \item (p.182) @{thm[mode=Rule] Un_insert_left[no_vars]} 
      \hfill (@{text Un_insert_left})
  \end{itemize}\<close>

subsubsection \<open>Monotonía de varias operaciones (7.4.4)\<close>

text \<open>
  \begin{itemize}
    \item (p.188) @{thm[mode=Rule] Un_mono[no_vars]} 
      \hfill (@{text Un_mono})
  \end{itemize}
\<close>

section \<open>Teoría de conjuntos finitos\<close>

text \<open>\comentario{Poner las páginas y secciones y ordenar los lemas 
  según las páginas.}\<close> 

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
