# MC-lang

MC-lang è un progetto personale e accademico che mira a costruire formalmente un piccolo linguaggio funzionale puro, chiamato MC (MiniCaml). Il linguaggio è pensato per essere sufficientemente espressivo da permettere la reificazione della propria sintassi e semantica, in uno stile simile a OCaml, con tipi variant ricorsivi e pattern matching.

Il progetto si articola in due fasi principali:

- **Costruzione formale del linguaggio MC:** la sintassi astratta e la semantica operazionale vengono definite nel proof assistant Rocq. La semantica funge da specifica per un interprete implementato in Rocq, di cui si dimostrano correttezza e completezza rispetto a essa. L'interprete diventa così un meccanismo esecutivo verificato per i programmi MC.
- **Costruzione di MCR (MiniCaml reificato):** dimostrare che MC può usare i propri costrutti per rappresentare la propria sintassi astratta e una versione del suo interprete, semanticamente equivalente a quella definita in Rocq. Quest'ultimo è detto anche *metainterprete*.

## Stato del progetto

Questa repository contiene la formalizzazione del nucleo di MC e il relativo interprete in Rocq: la prima fase del progetto.

## Requisiti e compilazione

Il progetto è stato sviluppato con Coq 8.18.0. Nel mio ambiente installo e gestisco Coq tramite OPAM; OPAM è il gestore di pacchetti utilizzato per predisporre l'ambiente, non una dipendenza specifica del progetto.

Per compilare i file del progetto, dalla directory principale eseguire:

```sh
make -f CoqMakeFile
```

## Cosa non è stato formalizzato

La fase di lexing e parsing non rientra nell'obiettivo della formalizzazione; al momento MC non dispone quindi di strumenti propri per queste fasi. La sintassi astratta è stata scelta liberamente, in funzione di esigenze descrittive, dimostrative e stilistiche.

Per scrivere programmi MC si usa il parser estendibile di Rocq, che permette di introdurre un po' di zucchero sintattico e semplificare la scrittura. Le notazioni di Rocq, tuttavia, non sono un sostituto affidabile di un lexer e di un parser dedicati. Ritengo che realizzare questi strumenti semplificherebbe molto la seconda fase del progetto.

## Cosa è stato formalizzato

La semantica statica e quella dinamica di MC sono state formalizzate con un approccio *big-step* (o *natural operational semantics*). Le fasi di elaborazione e valutazione sono rappresentate da giudizi logici definiti induttivamente e collegate alle rispettive implementazioni eseguibili tramite teoremi di correttezza e completezza.

Quando opportuno, sono stati inoltre definiti e dimostrati teoremi che caratterizzano direttamente il comportamento di singole componenti dell'interprete.

## Risultati principali

Il risultato generale della prima fase è il collegamento formale tra l'interprete eseguibile e la semantica di MC. I principali risultati sono:

- **Correttezza dell'elaboratore** (`elab_correct`, `elaboration.v`): se i contesti sono ben formati e l'elaboratore restituisce `Ok e'`, allora il giudizio statico corrispondente è derivabile.
- **Completezza dell'elaboratore** (`elab_complete`, `elaboration.v`): se il giudizio statico è derivabile, l'elaboratore restituisce `Ok e'`.
- **Correttezza degli errori di elaborazione** (`elab_failure_correct`, `elaboration.v`): se, con contesti ben formati, l'elaboratore restituisce un errore, non esiste una derivazione del giudizio statico corrispondente.
- **Completezza degli errori di elaborazione** (`elab_failure_complete`, `elaboration.v`): se, con contesti ben formati, non esiste una derivazione del giudizio statico, l'elaboratore restituisce un errore.
- **Determinismo della semantica statica** (`Elab_deterministic`, `elaboration.v`): per una stessa espressione e gli stessi contesti, due risultati derivabili dell'elaborazione coincidono.
- **Correttezza del valutatore** (`eval_correct`, `evaluation.v`): se l'ambiente dei valori è ben formato e il valutatore, con fuel `n`, restituisce `Ok v`, allora il giudizio dinamico corrispondente è derivabile.
- **Completezza del valutatore** (`eval_complete`, `evaluation.v`): se esiste una derivazione del giudizio dinamico e `n` è un bound di fuel sufficiente per le sue sottoderivazioni, il valutatore restituisce `Ok v`.
- **Determinismo della semantica dinamica** (`EVal_deterministic`, `evaluation.v`): con ambiente ben formato e bound di fuel sufficienti per le derivazioni considerate, una stessa espressione non può produrre due valori diversi.

## Esempio: eseguire l'interprete

`programs.v` contiene alcuni programmi già scritti ed è il punto in cui provarne di nuovi usando le notazioni locali. Ogni componente dell'interprete è un termine Coq e può essere valutata, ad esempio, con `Eval vm_compute in C`. Questo comando usa la VM di Rocq per calcolare il risultato.

Le componenti possono essere valutate indipendentemente, ma l'esecuzione completa segue l'ordine della formalizzazione:

1. Si scrive un programma `P` usando le notazioni locali definite in `programs.v`.
2. Si traduce `P` nella sintassi del kernel, ottenendo `P'`:

	```coq
	Definition P' := desugar_Expr P.
	```

3. Si elabora staticamente `P'` a partire dagli ambienti statici vuoti `register_empty` e `c_env_empty`:

	```coq
	Definition R := elab P' [] register_empty c_env_empty.
	```

	Il risultato `R` indica se l'elaborazione è riuscita oppure ha prodotto un errore.
4. Se `R` contiene un programma elaborato `P''`, lo si valuta nell'ambiente vuoto `v_env_empty`, scegliendo un fuel `n` sufficiente:

	```coq
	Definition R' := eval n P'' v_env_empty.
	```

	Se l'elaborazione statica o la valutazione produce un errore, il risultato contiene il relativo messaggio; altrimenti `R'` contiene il valore `V`.
5. In caso di successo, si converte `V` in una stringa con `val_to_string V`.

Per eseguire automaticamente i passaggi dalla desugarizzazione alla stampa del risultato si può usare `run_interpreter P n`. Per esempio, il programma `mcr_ast` è già definito in `programs.v`:

```coq
Eval vm_compute in run_interpreter mcr_ast 1000.
```

## Architettura del progetto

L'ordine di lettura segue le componenti dell'interprete e le teorie associate:

1. `ids.v`, `primitives.v`: definiscono le proprietà richieste agli identificatori, ai tipi primitivi e alle operazioni primitive tramite strutture `Record`.
2. `env.v`: implementa ambienti generici, le operazioni su di essi e le loro proprietà fondamentali.
3. `surface_syntax.v`: definisce la sintassi di superficie, basata su una scelta concreta di tipi e operazioni primitive; gli identificatori restano generici.
4. `kernel_syntax.v`: definisce la sintassi astratta del kernel, su cui è costruita la semantica di MC.
5. `desugarer.v`: traduce le forme derivate della sintassi di superficie in forme primitive del kernel.
6. `type_theory.v`, `pattern_theory.v`: contengono definizioni e teoremi sui tipi e sui pattern.
7. `type_env.v`: implementa gli ambienti di tipi come liste di associazione e ne dimostra le proprietà fondamentali.
8. `result_type.v`: definisce la monade `Result` e le operazioni fondamentali.
9. `elaboration.v`: formalizza la semantica statica e implementa l'elaboratore, dimostrando i teoremi che li collegano.
10. `values.v`: definisce i valori di MC e le loro proprietà.
11. `evaluation.v`: formalizza la semantica dinamica e implementa il valutatore, dimostrando i teoremi che li collegano.
12. `pretty_printer.v`: converte i valori MC in stringhe.
13. `programs.v`: implementa gli identificatori e definisce notazioni locali. Qui si possono scrivere programmi MC e verificare il percorso dal desugarer alla valutazione.


                         
                  





 
  
