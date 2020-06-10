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
  natural para el desarrollo de métodos de razonamiento. Surgió con la
  lógica silogística de Aristóteles (384 - 322 a.C). En ella, los 
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
  deductivos. La lógica proposicional de Frege formó parte de la 
  escuela denominada logicismo. Su objetivo consistía en investigar 
  los fundamentos de las matemáticas con el fin de formalizarlos 
  lógicamente, para así realizar deducciones y razonamientos 
  válidos.

	En las últimas décadas, el desarrollo de la computación y la 
  inteligencia artificial ha permitido la formalización de las 
  matemáticas y la lógica mediante el lenguaje computacional. Entre las 
  principales aplicaciones de la lógica en la computación se encuentra 
  la verificación y síntesis automáticas de programas. De este modo, 
  podemos verificar distintos razonamientos, asicomo crear herramientas 
  de razonamiento automático que permitan el desarrollo de nuevos 
  resultados. 

  En este contexto nace Isabelle en 1986, desarrollada por Larry Paulson 
  de la Universidad de Cambridge y Tobias Nipkow del Techniche 
  Universität München. Isabelle es un demostrador interactivo que 
  facilita la formalización lógica de resultados y proporciona 
  herramientas para realizar deducciones. En particular, 
  Isabelle/HOL es una especificación de Isabelle para la lógica de 
  primer orden. 

  Fundamentalmente, como demostrador interactivo, Isabelle permite 
  verificar cada paso de una deducción de manera precisa. Además, 
  incorpora herramientas de razonamiento automático para mejorar la 
  productividad del proceso de demostración. Para ello, cuenta con una 
  extensa librería de resultados lógicos y matemáticos que han sido 
  formalizados y continúan en desarrollo por parte de proyectos como 
  \<open>The Alexandria Project: Large-Scale Formal Proof for the Working 
  Mathematician\<close>. Este proyecto comienza en 2017, dirigido por 
  Lawrence Paulson desde la Universidad de Cambridge. Tiene como 
  finalidad la formalización de distintas teorías para ampliar la 
  librería de Isabelle, junto con la creación de herramientas 
  interactivas que asistan a los matemáticos en el proceso de 
  formalización, demostración y búsqueda de nuevos resultados. 

  El objetivo de este trabajo es la formalización de elementos y 
  resultados destacados de la lógica proposicional en Isabelle/HOL. El 
  desarrollo teórico de los mismos se fundamenta en el libro 
  \<open>First-Order Logic and Automated Theorem Proving\<close> de Melvin Fitting. 
  Los tres capítulos tratados consisten en la sintaxis, semántica y, 
  finalmente, la versión proposicional del lema de Hintikka. Este último 
  fue desarrollado por el filósofo y lógico Jaakko Hintikka (1929- 2015) 
  como herramienta para probar la completitud de la lógica de 
  primer orden.

  En el primer capítulo sobre sintaxis se establecen inicialmente las
  variables proposicionales que conforman los elementos básicos del 
  alfabeto, junto con una serie de conectivas que actúan sobre ellas. 
  De este modo, se define por recursión el conjunto de las fórmulas 
  proposicionales como el menor conjunto de estructuras sintácticas 
  con dicho alfabeto y conectivas que contiene a las fórmulas
  básicas (una constante \<open>\<bottom>\<close> y las propias variables proposicionales, 
  llamadas fórmulas atómicas) y es cerrado mediante procedimientos de 
  formación de nuevas fórmulas a partir de otras, en los que intervienen 
  las conectivas. Como es habitual, dada esta definición 
  recursiva, se dispone de un esquema de inducción sobre fórmulas que
  nos permitirá probar los resultados expuestos. Del mismo modo, se 
  define recursivamente el conjunto de subfórmulas de una fórmula, 
  mostrando propiedades que describen la estructura de las mismas en 
  relación con las propias fórmulas. Finalmente se presenta la 
  fórmula \<open>\<top>\<close> a partir de la constante \<open>\<bottom>\<close>, y dos conectivas 
  generalizadas que permiten extender conectivas binarias a una lista de 
  fórmulas.  

  En el siguiente capítulo precisamos la semántica asociada a las 
  estructuras sintácticas. Para ello, se define una interpretación como 
  una aplicación que asocia un booleano a cada variable proposicional. 
  Por recursión sobre la estructura de las fórmulas proposicionales, 
  podemos definir el valor de una fórmula en una interpretación dada. 
  De este modo, se prueba que dicho valor queda unívocamente determinado 
  por la imagen que la interpretación asocia a cada variable
  proposicional que aparece en la fórmula. Las nociones semánticas se 
  extienden análogamente a las fórmulas formadas con conectivas 
  generalizadas.

  Posteriormente se introducen dos definiciones semánticas 
  fundamentales: modelo de una fórmula y fórmula satisfacible. 
  La primera hace referencia a una interpretación en la que el valor 
  de una fórmula dada es verdadero, mientras la segunda se trata de una
  fórmula para la que existe una interpretación que sea modelo suyo. 
  Ambas nociones se extienden a conjuntos de fórmulas. 
  Por otro lado, se define el concepto de tautología como aquella 
  fórmula cuyo valor es verdadero en toda interpretación. Para concluir 
  la sección, daremos una noción formal de consecuencia lógica. 

  El capítulo tercero, y último, tiene como objetivo probar el lema de
  Hintikka, que manifiesta la satisfacibilidad de ciertos conjuntos de
  fórmulas. Para ello define dicha clase de conjuntos, llamados 
  conjuntos de Hintikka, de modo que para cada uno de ellos se 
  determina paralelamente una interpretación asociada, garantizando que 
  esta es modelo de cada fórmula del conjunto.

  En lo referente a las demostraciones asistidas por Isabelle/HOL de
  los resultados formalizados a lo largo de las secciones, se elaborarán 
  dos tipos de pruebas correspondientes a dos tácticas distintas. En 
  primer lugar, se probará cada resultado siguiendo un esquema de 
  demostración detallado. En él utilizaremos únicamente y de manera 
  precisa las reglas de simplificación y definiciones incluidas en la 
  librería de Isabelle, prescindiendo de las herramientas de 
  razonamiento automático del demostrador. Para ello, se realiza una 
  búsqueda inversa en cada paso de la demostración automática hasta 
  llegar a un desarrollo de la prueba basado deducciones a partir de
  resultados elementales que la completen de manera rigurosa. En 
  contraposición, se evidenciará la capacidad de razonamiento 
  automático de Isabelle/HOL mediante la realización de una prueba 
  alternativa siguiendo un esquema de demostración automático. Para 
  ello se utilizarán las herramientas de razonamiento que han sido 
  elaboradas en Isabelle/HOL con el objetivo de realizar deducciones de 
  la manera más eficiente.\<close>

(*<*)
end
(*>*) 