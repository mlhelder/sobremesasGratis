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
	all cliente: Cliente, t:Time-first | cliente in (Lanchonete.clientes).t

	//cada cliente tem no maximo 5 pedidos
	all cliente: Cliente, t: Time-first | #(cliente.meu_pedido).t <= 5


	//cada pedido pertence a apenas um cliente
	all p: Pedido, t: Time-first | (one c: Cliente | p in (c.meu_pedido).t)

	// todos lanches e bebidas estão em um pedido
	all l: Lanche, t: Time-first | l in (Pedido.lanche).t
	all bebida: Bebida, t: Time-first | bebida in (Pedido.bebidas).t

	//cada pedido tem um lanche ou uma bebida
	all p : Pedido, t: Time-first | (some (p.bebidas).t) or (some (p.lanche).t)

	//cada bebida ou lanche pertence a apenas um pedido
	all b:Bebida, t: Time-first | (one p: Pedido| b in (p.bebidas).t)
	all l:Lanche, t: Time-first | (one p: Pedido| l in (p.lanche).t)



}

pred init [t : Time] {
	no (Lanchonete.clientes).t
	all p:Pedido | no (p.lanche).t and no (p.bebidas).t
	all c:Cliente | no (c.meu_pedido).t
 
}


pred addPedido[p:Pedido, c:Cliente, t,t':Time]{
	p !in (c.meu_pedido).t
	(c.meu_pedido).t' = (c.meu_pedido).t + p
	

}

pred show() {
//#meu_pedido = 2
}

run show for 7 but exactly 7 Pedido
