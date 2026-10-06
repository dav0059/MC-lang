# MC-lang

MC-lang è un progetto personale e accademico che mira a costruire formalmente un piccolo linguaggio funzionale puro, chiamato MC (MiniCaml). Il linguaggio è pensato per essere sufficientemente espressivo da permettere la reificazione della propria sintassi e semantica, in uno stile simile a OCaml, con tipi variant ricorsivi e pattern matching.

Il progetto si articola in due fasi principali:

- **Costruzione formale del linguaggio MC:** la sintassi astratta e la semantica operazionale vengono definite nel proof assistant Rocq. La semantica funge da specifica per un interprete implementato in Rocq, di cui si dimostrano correttezza e completezza rispetto a essa. L'interprete diventa così un meccanismo esecutivo verificato per i programmi MC.
- **Costruzione di MCR (MiniCaml reificato):** dimostrare che MC può usare i propri costrutti per rappresentare la propria sintassi astratta e una versione del suo interprete, semanticamente equivalente a quella definita in Rocq. Quest'ultimo è detto anche *metainterprete*.

## Stato del progetto

Questa repository contiene la formalizzazione del nucleo di MC e il relativo interprete in Rocq: la prima fase del progetto.

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


                         
                  





 
  
