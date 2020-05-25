(*<*) 
theory Introduccion
  imports 
    Main 
    "HOL-Library.LaTeXsugar" 
    "HOL-Library.OptionalSugar"
    "HOL-Library.Countable"
begin
(*>*)

(* chapter \<open>Introducción\<close> *)

text \<open>
  La lógica es una ciencia que consiste en la formalización del lenguaje 
  natural para el desarrollo de métodos de razonamiento. Surgió con 
  Aristóteles (384 - 322 a.C) al reunir ciertas ideas filosóficas sobre 
  el razonamiento, dando origen a la lógica silogística. En ella, los 
  silogismos son razonamientos fundamentados en la deducción de 
  conclusiones a partir de dos premisas iniciales. Entre otras, 
  introdujo la regla \<open>modus ponnens\<close>:

  \<open>P \<longrightarrow> Q\<close>

  \<open>P\<close>

  \rule{20mm}{0.1mm}

  \<open>Q\<close>

	Posteriormente, los estoicos (400-200 a.C) comenzaron a cuestionarse 
  temas relacionados con la semántica, como la naturaleza de la verdad. 
  Formularon la \<open>paradoja del mentiroso\<close>, que plantea una incongruencia 
  acerca de la veracidad del siguiente predicado.

  \<open>Esta oración es falsa.\<close>

  Sin embargo, no fue hasta el siglo XVII que el matemático y filósofo 
  Gottfried Wilhelm Leibniz (1646 – 1716) instaura un programa lógico 
  que propone la búsqueda de un sistema simbólico del lenguaje natural 
  junto con la matematización del concepto de validez. Estas ideas 
  fueron la principal motivación del desarrollo de la lógica moderna del 
  siglo XIX de la mano de matemáticos y filósofos como Bernard Bolzano 
  (1781 – 1848), George Boole (1815 – 1864), Charles Saunders Pierce 
  (1839 – 1914) y Gottlob Frege (1848 – 1925). Fue este último quien 
  introdujo el primer tratamiento sistemático de la lógica 
  proposicional. Frege basó su tesis en el desarrollo de una sintaxis 
  completa que combina el razonamiento de deducción de la silogística 
  aristotélica con la noción estoica de conectivas para relacionar 
  ideas. Paralelamente desarrolló una semántica asociada a dicha 
  sintaxis que permitiese verificar la validez de los procesos 
  deductivos. Esta lógica de predicados de Frege formó parte de la 
  escuela denominada \<open>logicismo\<close>. Su objetivo consistía en investigar 
  los fundamentos de las matemáticas con el fin de reducir sus conceptos 
  y principios a unos exclusivamente lógicos, para así realizar 
  deducciones y razonamientos válidos. 

	En las últimas décadas, el desarrollo de la computación y la 
  inteligencia artificial ha permitido la formalización de la lógica y 
  las matemáticas en lenguaje computacional. Entre las principales 
  aplicaciones de la lógica en la computación se encuentra la 
  verificación y síntesis automáticas de programas. De este modo, 
  podemos verificar distintos razonamientos, asicomo crear herramientas 
  de razonamiento automático que permitan el desarrollo de nuevos 
  resultados. 

  En este contexto nace Isabelle en 1986, desarrollada por Larry Paulson 
  de la Universidad de Cambridge y Tobias Nipkow del Techniche 
  Universität München. Isabelle es un demostrador interactivo que 
  permite la formalización de resultados matemáticos en términos de la 
  lógica y proporciona herramientas para realizar deducciones sobre 
  ellos. En particular, Isabelle/HOL es una especificación de Isabelle 
  para la lógica de primer orden. 

  Fundamentalmente, como demostrador interactivo, Isabelle permite 
  verificar cada paso de una deducción de manera precisa. Además, 
  incorpora herramientas de razonamiento automático para mejorar la 
  productividad del proceso de demostración. Para ello, cuenta con una 
  extensa librería de resultados lógicos y matemáticos que han sido 
  formalizados y continúan en desarrollo por parte de proyectos como 
  \<open>The Alexandria Project: Large-Scale Formal Proof for the Working 
  Mathematician\<close>. Este proyecto comienza en 2017,  dirigido por 
  Lawrence Paulson desde la Universidad de Cambridge. Tiene como 
  finalidad la formalización de resultados para ampliar la librería de 
  Isabelle, junto con la creación de herramientas interactivas que 
  asistan a los matemáticos en el proceso de formalización, demostración 
  y búsqueda de nuevos resultados. 

  El objetivo de este trabajo es la formalización de elementos 
  destacados de la lógica proposicional en Isabelle/HOL. El desarrollo 
  teórico de los mismos se fundamenta en el libro \<open>First-Order Logic and 
  Automated Theorem Proving\<close> de Melvin Fitting. Los tres capítulos 
  tratados consisten en la sintaxis, semántica y, finalmente, la 
  versión proposicional del lema de Hintikka. Este último fue 
  desarrollado por el filósofo y lógico Jaakko Hintikka (1929- 2015) 
  como herramienta para probar la completitud de la lógica de 
  primer orden. 

  En lo referente a las demostraciones asistidas por Isabelle/HOL de
  los resultados formalizados, se elaborarán dos tipos de pruebas, cada 
  una siguiendo una táctica distinta. En primer lugar, se probará cada 
  resultado siguiendo un esquema de demostración detallada que utilice 
  únicamente las reglas de simplificación y definiciones incluidas en 
  la librería de\\ Isabelle, prescindiendo de los procesos automáticos 
  del demostrador. Para ello, se realiza una búsqueda inversa en cada 
  paso de la demostración automática hasta llegar a un desarrollo basado 
  en resultados axiomáticos que completen de manera precisa y rigurosa 
  la prueba. En contraposición, se evidenciará la capacidad de 
  razonamiento automático de Isabelle/HOL mediante la realización de una 
  prueba alternativa siguiendo un esquema de demostración automático. 
  Para ello se utilizarán las herramientas de razonamiento que han sido 
  elaboradas en Isabelle/HOL con el objetivo de realizar deducciones de 
  la manera más eficiente.\<close>

(*<*)
end
(*>*) 