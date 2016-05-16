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




fact traces{
    init[first]
		all pre: Time-last | let pos = pre.next |
			some c:Cliente, p:Pedido |
			addPedido[p,c,pre,pos]
		
}

fact{

	//todos os clientes estão na lanchonete
	all cliente: Cliente, t:Time-first | cliente in clientesDaLanchonete[Lanchonete, t]

	//cada cliente tem no maximo 5 pedidos
	all cliente: Cliente, t: Time-first | #pedidosDeUmCliente[cliente, t] <= 5


	//cada pedido pertence a apenas um cliente
	all p: Pedido, t: Time-first | (one c: Cliente | p in pedidosDeUmCliente[c, t])

	// todos lanches e bebidas estão em um pedido
	all l: Lanche, t: Time-first | l in lanchesDeUmPedido[Pedido, t]
	all bebida: Bebida, t: Time-first | bebida in bebidasDeUmPedido[Pedido, t]

	//cada pedido tem um lanche ou uma bebida
	all p : Pedido, t: Time-first | (some (p.bebidas).t) or (some lanchesDeUmPedido[p, t])

	//cada bebida ou lanche pertence a apenas um pedido
	all b:Bebida, t: Time-first | (one p: Pedido| b in bebidasDeUmPedido[p, t])
	all l:Lanche, t: Time-first | (one p: Pedido| l in lanchesDeUmPedido[p, t])

	//Especificacao da Promocao 1
	all p: Promo_Um, t: Time-first | (#lanchesDeUmPedido[p, t] :> Salgado >= 2 and (#bebidasDeUmPedido[p, t] :> Suco >= 1 or #bebidasDeUmPedido[p, t] :> Refrigerante >= 1)) or (#lanchesDeUmPedido[p, t] :> Sanduiche >= 2 and (#bebidasDeUmPedido[p, t] :> Suco >= 1 or #bebidasDeUmPedido[p, t] :> Refrigerante >= 1))

	//Especificacao da Promocao 2
	all p: Promo_Dois, t: Time-first | (#lanchesDeUmPedido[p, t] :> Salgado >= 2 and #lanchesDeUmPedido[p, t] :> Sanduiche >= 1 and  #bebidasDeUmPedido[p, t] :> Refrigerante >= 1) or (#lanchesDeUmPedido[p, t] :> Sanduiche >= 2 and #lanchesDeUmPedido[p, t] :> Salgado >= 1 and  #bebidasDeUmPedido[p, t] :> Refrigerante >= 1)
	 


}

pred init [t : Time] {
	no clientesDaLanchonete[Lanchonete, t]
	all p:Pedido | no lanchesDeUmPedido[p, t] and no bebidasDeUmPedido[p, t]
	all c:Cliente | no pedidosDeUmCliente[c, t]
 
}


pred addPedido[p:Pedido, c:Cliente, t,t':Time]{
	p !in pedidosDeUmCliente[c, t]
	pedidosDeUmCliente[c, t'] = pedidosDeUmCliente[c, t] + p
	

}

fun clientesDaLanchonete [l: Lanchonete, t: Time] : set Cliente {
	(l.clientes).t
}

fun pedidosDeUmCliente [c: Cliente, t: Time] : set Pedido {
	(c.meu_pedido).t
}

fun lanchesDeUmPedido [p: Pedido, t: Time] : set Lanche {
	(p.lanche).t
}

fun bebidasDeUmPedido [p: Pedido, t: Time] : set Bebida {
	(p.bebidas).t
}

pred show() {
//#meu_pedido = 2
}

run show for 7 but exactly 7 Pedido
