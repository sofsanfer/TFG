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

text \<open>En este glosario se recoge la lista de los lemas y reglas usadas
  indicando la página del \href{http://bit.ly/2OMbjMM}{libro de HOL} 
  donde se encuentran.\<close>

section \<open>La base de lógica de primer orden (2)\<close>

text \<open>En Isabelle corresponde a la teoría 
  \href{http://bit.ly/38iFKlA}{HOL.thy}\<close>

subsection \<open>Lógica primitiva (2.1)\<close>

subsubsection \<open>Conectivas y cuantificadores definidos (2.1.2)\<close>

text \<open>
  \begin{itemize}
    \item (p.34) @{thm[mode=Rule] not_def[no_vars]} 
      \hfill (@{text not_def})
  \end{itemize}\<close>

subsection \<open>Reglas fundamentales (2.2)\<close>

subsubsection \<open>Reglas de congruencia para aplicaciones (2.2.2)\<close>

text \<open>
  \begin{itemize}
    \item (p.37) @{thm[mode=Rule] arg_cong[no_vars]} 
      \hfill (@{text arg_cong})
    \item (p.37) @{thm[mode=Rule] arg_cong2[no_vars]} 
      \hfill (@{text arg_cong2})
  \end{itemize}\<close>

subsubsection \<open>Negación (2.2.7)\<close>

text \<open>
  \begin{itemize}
    \item (p.39) @{thm[mode=Rule] notI[no_vars]} 
      \hfill (@{text notI})
    \item (p.39) @{thm[mode=Rule] notE[no_vars]} 
      \hfill (@{text notE})
  \end{itemize}\<close>

subsubsection \<open>Disyunción I (2.2.9)\<close>

text \<open>
  \begin{itemize}
    \item (p.40) @{thm[mode=Rule] disjE[no_vars]} 
      \hfill (@{text disjE})
  \end{itemize}\<close>

subsubsection \<open>Conjunción (2.2.14)\<close>

text \<open>
  \begin{itemize}
    \item (p.41) @{thm[mode=Rule] conjI[no_vars]} 
      \hfill (@{text conjI})
    \item (p.41) @{thm[mode=Rule] conjunct1[no_vars]} 
      \hfill (@{text conjunct1})
    \item (p.41) @{thm[mode=Rule] conjunct2[no_vars]} 
      \hfill (@{text conjunct2})
  \end{itemize}\<close>

subsection \<open>Configuración del paquete (2.3)\<close>

subsubsection \<open>Simplificadores (2.3.4)\<close>

text \<open>
  \begin{itemize}
    \item (p.50) @{thm[mode=Rule] not_False_eq_True[no_vars]} 
      \hfill (@{text not_False_eq_True})
    \item (p.53) @{thm[mode=Rule] not_ex[no_vars]} 
      \hfill (@{text not_ex})
  \end{itemize}\<close>

section \<open>Teoría de conjuntos para lógica de orden superior (7)\<close>

text \<open>Los siguientes resultados corresponden a la teoría de conjuntos 
  \href{https://n9.cl/qatp}{Set.thy}.\<close>

subsection \<open>Subconjuntos y cuantificadores acotados (7.2)\<close>

text \<open>
  \begin{itemize}
    \item (p.163) @{thm[mode=Rule] ballI[no_vars]} 
      \hfill (@{text ballI})
  \end{itemize}\<close>

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
    \item (p.167) @{thm[mode=Rule] ball_empty[no_vars]} 
      \hfill (@{text ball_empty})
    \item (p.167) @{thm[mode=Rule] bex_empty[no_vars]} 
      \hfill (@{text bex_empty})
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
  \end{itemize}\<close>

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
    \item (p.172) @{thm[mode=Rule] singleton_iff[no_vars]} 
      \hfill (@{text singleton_iff})
  \end{itemize}
\<close>

subsection \<open>Más operaciones y lemas (7.4)\<close>

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
    \item (p.187) @{thm[mode=Rule] ball_simps[no_vars]} 
      \hfill (@{text ball_simps})
  \end{itemize}\<close>

subsubsection \<open>Monotonía de varias operaciones (7.4.4)\<close>

text \<open>
  \begin{itemize}
    \item (p.188) @{thm[mode=Rule] Un_mono[no_vars]} 
      \hfill (@{text Un_mono})
    \item (p.188) @{thm[mode=Rule] imp_refl[no_vars]} 
      \hfill (@{text imp_refl})
  \end{itemize}
\<close>

section \<open>Nociones sobre funciones (9)\<close>

text \<open>En Isabelle, la teoría de funciones se corresponde con 
  \href{http://bit.ly/2P9NWwq}{Fun.thy}\<close>

subsection \<open>Actualización de funciones (9.6)\<close>

text \<open>
  \begin{itemize}
    \item (p.213) @{thm[mode=Rule] fun_upd_other[no_vars]} 
      \hfill (@{text fun_upd_other})
  \end{itemize}\<close>

section \<open>Retículos completos (10)\<close>

text \<open>En Isabelle corresponde a la teoría 
  \href{http://bit.ly/2wimZjA}{Complete-Lattices.thy}\<close>

subsection \<open>Retículos completos en conjuntos (10.6)\<close>

subsubsection \<open>Unión (10.6.3)\<close>

text \<open>
  \begin{itemize}
    \item (p.238) @{thm[mode=Rule] Union_empty[no_vars]} 
      \hfill (@{text Union_empty})
  \end{itemize}\<close>

section \<open>Conjuntos finitos (18)\<close>

text \<open>A continuación se muestran resultados relativos a la teoría 
  \href{https://n9.cl/x86r}{FiniteSet.thy}.\<close> 

subsection \<open>Predicado de conjuntos finitos (18.1)\<close>

text \<open>
  \begin{itemize}
    \item (p.419) @{thm[mode=Def] finite[no_vars]} 
      \hfill (@{text finite})
  \end{itemize}\<close>

subsection \<open>Finitud y operaciones de conjuntos comunes (18.2)\<close>

text\<open>  
  \begin{itemize}
    \item (p.422) @{thm[mode=Rule] finite_UnI[no_vars]} 
      \hfill (@{text finite_UnI})
  \end{itemize}\<close>

section \<open>El tipo de datos de la listas finitas (66)\<close>

text \<open>En esta sección se muestran resultados sobre listas finitas 
  dentro de la teoría de listas de Isabelle 
  \href{http://bit.ly/2se9Oy0}{List.thy}\<close>

text\<open>  
  \begin{itemize}
    \item (p.1169) @{thm[mode=Rule] list.set[no_vars]} 
      \hfill (@{text list.set})
  \end{itemize}\<close>

subsection \<open>Funciones básicas de procesamiento de listas (66.1)\<close>

subsubsection \<open>Función \<open>set\<close>\<close>

text\<open>  
  \begin{itemize}
    \item (p.1195) @{thm[mode=Rule] set_append[no_vars]} 
      \hfill (@{text set_append})
  \end{itemize}\<close>

(*<*)
end
(*>*) 
