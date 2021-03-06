module olavo

open util/ordering[Time] as to

sig Time{}


one sig Lanchonete {
	clientes : set Cliente -> Time

}

sig Cliente {
	meu_pedido : set Pedido -> Time
}

abstract sig Pedido{
	 lanche : set Lanche -> Time,
	 bebidas : set Bebida -> Time
}

sig Pedido_Simples extends Pedido{}
sig Promo_Um extends Pedido{}
sig Promo_Dois extends Pedido{}

abstract sig Lanche{}

abstract sig Salgado extends Lanche{}
sig Coxinha extends Salgado{}
sig Empada extends Salgado{}
sig Pastel extends Salgado{}

abstract sig Sanduiche extends Lanche{}
sig Sanduiche_de_Atum extends Sanduiche{}
sig Sanduiche_de_Frango extends Sanduiche{}

abstract sig Bebida{}
sig Agua extends Bebida{}
sig Refrigerante extends Bebida{}
sig Suco extends Bebida{}

abstract sig Sobremesa extends Lanche{ }
sig Pudim extends Sobremesa{}
sig Fatia_de_Torta extends Sobremesa{}
sig Brigadeiro extends Sobremesa{}



------------------------------------------------------------------------- FATOS -------------------------------------------------------------------------

fact traces{
    init[first]
		all pre: Time-last | let pos = pre.next |
			some c:Cliente, p:Pedido , l:Lanche, b:Bebida, s:Sobremesa |
			addPedido[p,c,pre,pos] or
			addComida[p,l,pre,pos] or
			addBebida[p,b,pre,pos] or
			addSobremesa[p,s,pre,pos]
		
}

fact {
	//Quantidade de itens
	#Lanche <= 15
	#Salgado <= 15
	#Sanduiche <= 10
	#Bebida <= 10
	#Sobremesa <= 5
}

fact{

	//todos os clientes estão na lanchonete
	all cliente: Cliente, t:Time-first | cliente in clientesDaLanchonete[Lanchonete, t]

	//cada cliente tem no maximo 2 pedidos
	all cliente: Cliente, t: Time-first | #pedidosDeUmCliente[cliente, t] <= 5 and #pedidosDeUmCliente[cliente, t] >= 1

	//cada pedido pertence a apenas um cliente
	all p: Pedido, t: Time-first | (one c: Cliente | p in pedidosDeUmCliente[c, t])

	// todos lanches e bebidas estão em um pedido
	all l: Lanche, t: Time-first | l in lanchesDeUmPedido[Pedido, t]
	all bebida: Bebida, t: Time-first | bebida in bebidasDeUmPedido[Pedido, t]

	//cada pedido tem um lanche ou uma bebida
	all p : Pedido, t: Time-first | (some bebidasDeUmPedido[p, t]) or (some lanchesDeUmPedido[p, t])

	//cada bebida ou lanche pertence a apenas um pedido
	all b:Bebida, t: Time-first | (one p: Pedido| b in bebidasDeUmPedido[p, t])
	all l:Lanche, t: Time-first | (one p: Pedido| l in lanchesDeUmPedido[p, t])

	//Especificacao da Promocao 1
	all p: Promo_Um, t: Time-first | isPromocaoUm[p , t]

	//Especificacao da Promocao 2
	all p: Promo_Dois, t: Time-first | isPromocaoDois[p, t]
	
	//Restringe que os pedidos simples não sejam promoções	
	all p: Pedido_Simples, t: Time-first | !isPromocaoUm[p , t] and !isPromocaoDois[p , t]

}

------------------------------------------------------------------------- PREDICADOS -------------------------------------------------------------------------


pred init [t : Time] {
	no clientesDaLanchonete[Lanchonete, t]
	all p:Pedido | no lanchesDeUmPedido[p, t] and no bebidasDeUmPedido[p, t]
	all c:Cliente | no pedidosDeUmCliente[c, t]
 
}

// Adiciona os pedidos aos clientes.
pred addPedido[p:Pedido, c:Cliente, t,t':Time]{
	p !in pedidosDeUmCliente[c, t]
	pedidosDeUmCliente[c, t'] = pedidosDeUmCliente[c, t] + p
	
}
// Adiciona comida ao pedido

pred addComida[p: Pedido, l:Lanche , t, t': Time]{
	l !in (p.lanche).t
	(p.lanche).t' = (p.lanche).t + l
}

// Adiciona Bebida ao pedido
pred addBebida[p: Pedido, b:Bebida, t, t': Time]{
	b !in (p.bebidas).t
	(p.bebidas).t' = (p.bebidas).t + b
}

// Adiciona sobremesa ao pedido
pred addSobremesa[p: Pedido, s:Sobremesa, t, t': Time]{
	s !in (p.lanche).t
	(p.lanche).t' = (p.lanche).t + s
}


/* Especificação da Promoção 1 mais estrita
Se o pedido tiver 2 ou mais Salgados então não tem nenhum Sanduiche e tem que ter um Suco e nenhum Refrigerante 
ou então um Refrigerante e nenhum Suco (não pode ter Suco e Refrigerante ao mesmo tempo)
ou se o pedido tiver 2 ou mais Sanduiches então não tem nenhum Salgado  e tem que ter um Suco
e nenhum Refrigerante ou então um Refrigerante e nenhum Suco (não pode ter Suco e Refrigerante ao mesmo tempo).
O pedido não pode ter Agua e nem Fatia de Torta. Só pode ter um Brigadeiro e nenhum Pudim ou então um Pudim e nenhum Brigadeiro (nunca os dois ao mesmo tempo).*/
pred isPromocaoUm[p: Pedido, t: Time] {
	(((((#lanchesDeUmPedido[p, t] :> Salgado >= 2 and no lanchesDeUmPedido[p, t] :> Sanduiche) and ((one bebidasDeUmPedido[p, t] :> Suco and no bebidasDeUmPedido[p, t] :> Refrigerante)
	or (one bebidasDeUmPedido[p, t] :> Refrigerante and no bebidasDeUmPedido[p,t ] :> Suco))) or ((#lanchesDeUmPedido[p, t] :> Sanduiche >= 2 and no lanchesDeUmPedido[p, t] :> Salgado)
	and ((one bebidasDeUmPedido[p, t] :> Suco and no bebidasDeUmPedido[p, t] :> Refrigerante) or (one bebidasDeUmPedido[p, t] :> Refrigerante and no bebidasDeUmPedido[p, t] :> Suco))))
	and no bebidasDeUmPedido[p,t] :> Agua) and no lanchesDeUmPedido[p, t] :> Fatia_de_Torta) and ((one lanchesDeUmPedido[p, t] :> Brigadeiro and no lanchesDeUmPedido[p, t] :> Pudim)
	or (one lanchesDeUmPedido[p, t] :> Pudim and no lanchesDeUmPedido[p, t] :> Brigadeiro))
}

/*Especificação da Promoção 1 menos estrita
O pedido deve ter 2 ou mais Salgados e ao menos um Suco ou Refrigerante (pode vir os dois) ou então
o pedido deve ter 2 ou mais Sanduiches e ao menos um Suco ou Refrigerante (pode vir os dois). Nessa especificação pode vir
também Agua, todas as Sobremesas e pode ter também lanches de duas categorias (Sanduiche e Salgado).
pred isPromocaoUm[p: Pedido, t: Time] {
	(#lanchesDeUmPedido[p, t] :> Salgado >= 2 and (some bebidasDeUmPedido[p,t] :> Suco or some bebidasDeUmPedido[p,t] :> Refrigerante))
	or (#lanchesDeUmPedido[p, t] :> Sanduiche >= 2 and (some bebidasDeUmPedido[p,t] :> Suco or some bebidasDeUmPedido[p,t] :> Refrigerante))
}
*/

/* Especificação da Promoção 2 mais estrita
O pedido deve ter 2 Salgados e mais de um Sanduiche e um Refrigerante ou deve ter 2 Sanduiches e mais de um Salgado e um Refrigerante.
O pedido deve ter também uma Fatia_de_Torta. O pedido não pode ter Pudim, nem Brigadeiro, nem Suco e nem Agua.*/
pred isPromocaoDois[p: Pedido, t: Time] {
	(((((((#lanchesDeUmPedido[p, t] :> Salgado = 2 and some lanchesDeUmPedido[p, t] :> Sanduiche) and one bebidasDeUmPedido[p, t] :> Refrigerante)
	or ((#lanchesDeUmPedido[p, t] :> Sanduiche = 2 and some lanchesDeUmPedido[p, t] :> Salgado) and  one bebidasDeUmPedido[p, t] :> Refrigerante))
	and one lanchesDeUmPedido[p, t] :> Fatia_de_Torta) and no lanchesDeUmPedido[p,t] :> Pudim) and no lanchesDeUmPedido[p,t] :> Brigadeiro)
	and no bebidasDeUmPedido[p, t] :> Suco) and no bebidasDeUmPedido[p, t] :> Agua
}

/*Especicação da Promoção 2 menos estrita
O pedido deve ter 2 ou mais Salgados, ao menos um Sanduiche e ao menos um Refrigerante ou então
o pedido deve ter 2 ou mais Sanduiches, ao menos um Salgado e ao menos um Refrigerante.
O pedido pode ter Suco,Agua e todas as Sobremesas.
pred isPromocaoDois[p: Pedido, t: Time] {
	(#lanchesDeUmPedido[p, t] :> Salgado >= 2 and some lanchesDeUmPedido[p, t] :> Sanduiche and  some bebidasDeUmPedido[p, t] :> Refrigerante)
	or (#lanchesDeUmPedido[p, t] :> Sanduiche >= 2 and some lanchesDeUmPedido[p, t] :> Salgado and  some bebidasDeUmPedido[p, t] :> Refrigerante)
}
*/




------------------------------------------------------------------------- FUNÇÕES -------------------------------------------------------------------------

//Funcao que retorna o conjunto de clientes da Lanchonete
fun clientesDaLanchonete [l: Lanchonete, t: Time] : set Cliente {
	(l.clientes).t
}

 //Funcao que retorna o conjunto de pedidos de um Cliente
fun pedidosDeUmCliente [c: Cliente, t: Time] : set Pedido {
	(c.meu_pedido).t
}

//Funcao que retorna o conjunto de lanches de um Pedido
fun lanchesDeUmPedido [p: Pedido, t: Time] : set Lanche {
	(p.lanche).t
}

//Funcao que retorna o conjunto de bebidas de um Pedido
fun bebidasDeUmPedido [p: Pedido, t: Time] : set Bebida {
	(p.bebidas).t
}

fun sobremesasDeUmPedido[p:Pedido,t:Time]: set Lanche{
((p.lanche).t & (Pudim + Fatia_de_Torta + Brigadeiro))
}

------------------------------------------------------------------------- ASSERTS -------------------------------------------------------------------------

assert promoUm{
	/*
	* Procura um pacote um que nao atende as especificaçao do pacote
	*/
	!some p: Promo_Um, t: Time-first | no bebidasDeUmPedido[p,t]  and 	#((lanchesDeUmPedido[p,t]) & (Coxinha + Pastel + Empada)) < 2 and 
	#((lanchesDeUmPedido[p,t]) & (Sanduiche_de_Frango + Sanduiche_de_Atum)) < 2 and #((lanchesDeUmPedido[p,t]) & (Pudim +Fatia_de_Torta + Brigadeiro)) < 2 
}

assert noPedidoVazio{
	/*
	* Procura um pedido que nao tenha nem comida nem bebida
	*/
	!some p: Pedido | no p.bebidas and no p.lanche
}

assert noPedidoSemCliente {
	/*
	* Procura se exite pedido sem cliente
	*/
	!some p: Pedido| all t: Time-first | (all c: Cliente | p !in (c.meu_pedido).t) 
}

------------------------------------------------------------------------- CHECKS -------------------------------------------------------------------------


//check noPedidoVazio for 20

//check noPedidoSemCliente for 20

//check promoUm for 20





pred show() {
//#meu_pedido = 2
}

run show for 10 but exactly 2 Promo_Um
