# Linguagem Intermediaria (foco LLVM)
- reg temporarios (regs virtuais)
- instrucoes de 3 enderecos (eg. r1 = r2 + r3)
- bloco basico (instrucoes executadas linearmente, sem jmps ou labels no meio, jmp termina um bloco basico)
- funcoes com parametros
- tipada

- SSA - Single Static Assignment
	- Cada temporario tem apenas uma atribuicao a ele no codigo inteiro (LLVM usa apenas isso)
	- Soh deve existir uma linha que atribui valor a variavel, mas esta linha pode ser executada n vezes e com valores diferentes
	- temporarios viram meros transportadores dos resultados
	- Problemas em loops, contador precisaria ser mutado. Para isso se usa  funcao "phi".
		eg.: v = phi(start -> v1, L1 -> v2): v eh v1 se vindo de start, ou v2 se vindo de L1
- llvm nao suporta assinar constantes a temporarios

- variaveis vivas
	- variaveis cujo valor ainda eh usado
	Bin = (Bout - Definidas()) + Used (B)
	Bout = U B'in
        B'e succ(B)

