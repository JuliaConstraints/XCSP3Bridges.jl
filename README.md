# XCSP3Bridges — reconstruction

Cette version rétablit un module Julia de réseaux apprenables et leur compilation
en MILP par les bridges de ConstraintProgrammingExtensions (CPE). Les sources de
l'ancien module n'ont pas été retrouvées : ce dépôt est une reconstruction avec
un nouveau UUID et une numérotation explicitement versionnée, pas une restauration
à l'identique des anciens rangs.

## Représentation et interfaces

`NetworkSpace(domains; slots, operators, constants, budgets...)` fixe uniquement
les domaines finis, la capacité, les opérations autorisées et les limites.
Il n'embarque aucun nom de contrainte, oracle, solution ou table globale de
satisfaction. Les constantes font partie des décisions du réseau ; `:constant`
est ajouté à l'alphabet du constructeur par domaines s'il est absent.

Un `Network` possède `5slots + 1` décisions entières : pour chaque emplacement,
opération, trois ports antérieurs et constante ; la dernière décision choisit
la sortie. `decode_network` utilise le décodeur générique de QUBOConstraints Q12
et produit un `Program`. `satisfies(program, assignment)` évalue ce graphe.
Un emplacement inactif doit avoir une charge nulle. Les sorties sont booléennes.
Les tableaux du modèle et du programme sont possédés et doivent rester en lecture
seule ; les poids fournis au décodeur peuvent ensuite être modifiés librement.

Le socle atomique est partagé avec QUBOConstraints ; cette première version ne
réintroduit pas un deuxième moteur de décodage ou une seconde banque de recettes.
Elle couvre son alphabet entier : arithmétique entière, comparaisons, logique,
distance, opérations totales explicites et conditionnelle. Les expressions
partielles indéfinies sur leurs domaines locaux sont refusées.

`network_count`, `network_at` et `network_rank` exposent aussi une bijection entre
rangs **BigInt** et graphes structurellement valides. Un rang n'atteste pas la
validité sémantique : division par zéro, sortie non booléenne ou budget dépassé
sont contrôlés par le décodeur. Aucun filtre ne consulte la contrainte recherchée.
Les emplacements inactifs viennent d'abord, puis les opérations dans l'ordre de
l'alphabet, leurs ports dans l'ordre lexicographique, et les racines disponibles
dans l'ordre topologique. La constante zéro vient d'abord lorsqu'elle appartient
à l'intervalle, puis les autres valeurs en ordre croissant.

Le rang zéro sélectionne la première entrée lorsque des entrées existent.
Le comptage utilise une table triangulaire de taille quadratique en `slots`,
avec des budgets explicites `max_rank_states` et `max_rank_bits`.
`decision_domains` expose les bornes indépendantes des poids aux optimiseurs ;
le décodeur contrôle en plus les dépendances, arités et types.

## Exemple et compilation

```julia
import XCSP3Bridges as XB

space = XB.NetworkSpace([0:2, 0:2]; slots=1, operators=(:eq,), constants=0:1)
eq = findfirst(==(:eq), space.operators)
weights = BigInt[eq, 1, 2, 0, 0, 3]
program = XB.decode_network(space, weights)
@assert XB.satisfies(program, [1, 1])
@assert !XB.satisfies(program, [1, 2])

milp = XB.compile_milp(program)
# milp.linear : modèle MOI primitif ; milp.sources : indices des entrées.
# Avec un optimiseur MOI : map = MOI.copy_to(optimizer, milp.linear).

payload = XB.network_payload(space, weights)
fresh, network = XB.restore_network(payload)
@assert XB.network_at(fresh, XB.network_rank(fresh, network)).weights == weights
```

La compilation fixe la racine à 1, impose les domaines de toutes les entrées,
y compris les entrées inutilisées, et convertit chaque relation fonctionnelle
locale à l'aide de `CPE.Domain2MILPBridge` et `CPE.VectorDomain2MILPBridge`.
La projection du MILP sur les sources correspond à `satisfies`.
Les ports partagés gardent la même variable ; une relation n'est jamais remplacée
par des copies indépendantes de ses entrées.

`add_bridges!(lazy_optimizer)` enregistre les deux bridges CPE.
`add_program!(lazy_optimizer, program, source_variables)` permet de raccorder
un programme à des variables existantes, y compris des sources aliasées ;
il retourne les contraintes et auxiliaires ajoutés. Cette API ajoute des
relations MOI directement ; elle ne définit pas un nouveau type de set MOI.
`bridge_payload` et `restore_bridge` sauvegardent/restaurent un MILP entier creux.
Les entiers doivent être exactement représentables en Float64 pour ce backend.

Les refus de ressources sont des `BudgetExceeded`, distincts des programmes
mal formés (`ArgumentError`, `DimensionMismatch`). Le dépassement d'un budget
ne prouve aucune impossibilité de représentation.

## Apprentissage et benchmarks

`train(space, assignments, labels; max_candidates, initial_weights, start_rank)`
est un petit apprenant énumératif borné sur les rangs publics. Il retourne le
meilleur réseau, son nombre de désaccords, les candidats refusés et le statut.
`training_fit` désigne seulement un accord sur le corpus fourni. L'initialisation
manuelle compte comme un candidat et passe le décodeur normal. Ce moteur sert de
référence technique, pas d'algorithme efficace pour les espaces à 256 emplacements.
Les pilotes HPO peuvent exploiter soit les poids, soit les rangs.

L'adaptateur `BridgeAdapter` de ConstraintLearningBenchmarks utilise de nouveau
`NetworkSpace`, `network_count`, `network_at`, `decode_network`, `satisfies` et
`BudgetExceeded`. Son identifiant comprend la nouvelle version de représentation,
afin de distinguer les nouvelles campagnes des anciens rangs.

Les **637 témoins** restent dans une seule banque, sans copie dans ce package :
[catalogue](../ConstraintLearningBenchmarks/perf/core_witnesses/bank/catalog.toml),
[variantes Core](../ConstraintLearningBenchmarks/perf/core_witnesses/bank/VARIANTS.md).
`load_witness(path)` importe directement leurs modèles Q12 et poids, sans lire
leurs labels ou utiliser une recette Core. La banque offre une référence par
forme Core, pas une qualification sur toutes les tailles ou tous les paramètres
possibles. Ces témoins manuels ne sont pas déclarés optimaux.

## Environnement et validation

Les packages en développement se trouvent côte à côte sous `~/.julia/dev`.
L'environnement explicite des témoins sélectionne les versions locales ; le
package de bibliothèque ne contient pas de chemins machine dans ses dépendances.

Depuis `~/.julia/dev/ConstraintLearningBenchmarks` :

```sh
julia --project=perf/core_witnesses -e 'using Pkg; Pkg.instantiate()'
julia --project=perf/core_witnesses -e 'using Pkg; Pkg.test("XCSP3Bridges")'
julia --compile=min -O0 --project=perf/core_witnesses perf/core_witnesses/qualify_bridges.jl
```

Le dernier contrôle reconstruit les 637 programmes depuis leurs seuls modèles
et poids, compare leurs sorties aux labels précédemment qualifiés, conserve les
empreintes des MILP sauvegardés et relance HiGHS sur les **6 886 affectations**.
Il désactive les entrées de recettes Core et ne charge ni registre de cas ni
oracle. Un chemin de rapport peut être passé comme deuxième argument, après le
dossier de banque ; sans ce chemin, le contrôle n'écrit aucun résultat.

Les tests du package vérifient la bijection des rangs, le décodeur, la possession
des données, la sérialisation, les refus, la faisabilité MILP, les aliases et un
petit apprentissage sans témoin initial. Le contrôle d'intégration natif séparé
est `ConstraintLearningBenchmarks/test/evolving_bridges.jl` : il utilise la vraie
grammaire MetaStrategist et archive/recharge les candidats dans un dossier
temporaire. Il ne constitue pas une comparaison de performances entre solveurs.
