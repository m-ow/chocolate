## Introducción

Bienvenidos sean al laboratorio del curso de Semántica y Verificación. Soy su ayudante de laboratorio, Juan Pablo.

Durante el curso vamos a estudiar distintas estrategias semánticas para el análisis de programas y la verificación de su comportamiento contra una especificación dada.

En el laboratorio nos vamos a enfocar en utilizar un lenguaje de programación con tipos dependientes, que es una de las herramientas más poderosas en el ámbito de la verificación. En esta ocasión, hemos elegido a [Lean](https://lean-lang.org/) como nuestro lenguaje. Esta elección es debido a su similitud con otros lenguajes declarativos, por su asistente interactivo de pruebas integrado, y por su popularidad creciente tanto en la academia como en la industria. Una alternativa podría ser [~~Coq~~ Rocq](https://coq.inria.fr/) que también es popular en el área de verificación de software; sin embargo, puede parecer un poco menos amigable como un primer acercamiento a este tipo de lenguajes.

Utilizaremos Lean para formalizar algunas definiciones y teoremas, certificando que nuestro trabajo es correcto. En particular será de interés formalizar un lenguaje imperativo, y mostrar teoremas acerca de este desde las distintas semánticas que se ven en el curso. Por supuesto, esto será posterior a la introducción que se dará el lenguaje, para batallar con la curva de aprendizaje lo menos posible.

## Sobre la instalación

Para el curso utilizaremos archivos `.lean`, con el código disponible para ejecutarse o visualizarse en el Panel de Información (conocido como _Infoview_) que incluyen los editores de código con su respectivo modo para código de Lean. Además, se incluyen comentarios explicando el comportamiento y el contenido importante.

El material que se utilice lo podrás encontrar en el [repositorio del curso](https://github.com/jpyamamoto/syv-20252). Se recomienda hacer un _fork_ y procurar tener tus cambios en una rama distinta a la principal, para no tener conflictos en las actualizaciones.

Se utilizará durante el curso la versión de Lean número 4. Debido a que esta versión es relativamente reciente, y que la versión 3 tuvo mucho alcance, es posible encontrar material en internet que no compila en la versión más actual. Al revisar fuentes, procura revisar que se esté utilizando Lean 4.

Es importante que tengas tu propia instalación de Lean, para ello puedes remitirte a la [guía oficial de instalación](https://leanprover-community.github.io/get_started.html). También es recomendable revisar alguno de los siguientes enlaces según tu editor preferido:

- [Visual Studio Code:](https://lean-lang.org/lean4/doc/quickstart.html) El editor "oficial" para código de Lean. Esta es la instalación sugerida, y es la que usaré durante el curso para asemejar lo más cercano a su experiencia.
- [Neovim:](https://github.com/Julian/lean.nvim) Plugin con soporte constante y en general buena interacción. Personalmente suelo utilizar esta opción.
- [Emacs:](https://github.com/leanprover-community/lean4-mode) Modo para Lean 4, no cuenta con evil mode. Lo utilicé brevemente y es un buen paquete, no estoy al tanto de su mantenimiento en tiempos recientes.

Además, existen otras alternativas para ejecutar Lean.

### Lean 4 Web

**URL:** [https://live.lean-lang.org/](https://live.lean-lang.org/)

Versión en línea del editor, que incluye el paquete de Mathlib (biblioteca popular con la formalización de una amplia diversidad de áreas de las matemáticas).

No es recomendable para el curso, puesto que utilizaremos nuestra propia biblioteca estándar. Puede ser útil para experimentos pequeños.

### GitHub Codespaces

**URL:** [https://github.com/jpyamamoto/syv-20252](https://github.com/jpyamamoto/syv-20252)

Adicional al material del curso, el repositorio está configurado para poder ejecutar su propia instancia de VScode en el navegador. Esto te permitirá correr todo el ambiente que esperarías tener en tu instalación local, pero disponible a través del navegador.

La opción más recomendada es la instalación local, pero esta es una buena alternativa. Cuida subir tus cambios a tu repositorio, para no perder los avances.

## Sobre el material

A lo largo del curso utilizaré material adaptado del curso [Hitchhiker's Guide to Logical Verification (2024 Edition)](https://lean-forward.github.io/hitchhikers-guide/2024/) impartido por Anne Baanen, Alexander Bentkamp, Jasmin Blanchette, Johannes Hölzl, y Jannis Limperg. Este material es desarrollado como parte del proyecto [Lean Forward](https://lean-forward.github.io/).

Además de los archivos de Lean que usaremos, puedes revisar el libro de texto ["The Hitchhiker's Guide to Logical Verification"](https://github.com/lean-forward/logical_verification_2024/raw/main/hitchhikers_guide_2024_desktop.pdf).

## Material Extra

A continuación dejo algunos enlaces a otras referencias que pueden resultar de utilidad para aprender y practicar el uso de Lean.

- [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/): Un libro digital que introduce Lean desde el enfoque de la programación funcional.
- [Theorem Proving in Lean](https://leanprover.github.io/theorem_proving_in_lean4/): Un libro digital que introduce a Lean utilizando el enfoque de la realización de demostraciones matemáticas.
- [Formalising Mathematics](https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2024/): Acompañamiento de un curso en donde se enseña Lean aplicado a distintas áreas matemáticas como la teoría de conjuntos, grupos, espacios topológicos, teoría de números, y más.
- [The Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4): Un curso interactivo en línea donde se construye cierta teoría sobre los números naturales y se demuestran teoremas varios sobre operaciones aritméticas.
