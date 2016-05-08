module olavo

one sig Lanchonete {
	clientes : set Cliente
}

sig Cliente {
	pedidos : Pedido
}

abstract sig Pedido{
	 lanche : set Lanche,
	 bebidas : set Bebida
}

sig Pedido_Simples extends Pedido{
}

sig Promo_Um extends Pedido{
}

sig Promo_Dois extends Pedido{
}


abstract sig Lanche{
}

abstract sig Salgado extends Lanche{ 
	
}

sig Coxinha extends Salgado{
}

sig Empada extends Salgado{
}

sig Pastel extends Salgado{
}



abstract sig Sanduiche extends Lanche{ 
}

sig Sanduiche_de_Atum extends Sanduiche{
}

sig Sanduiche_de_Frango extends Sanduiche{
}


abstract sig Bebida{
}

sig Agua extends Bebida{
}

sig Refrigerante extends Bebida{
}

sig Suco extends Bebida{
}


abstract sig Sobremesa extends Lanche{ 
}
sig Pudim extends Sobremesa{
}

sig Fatia_de_Torta extends Sobremesa{
}

sig Brigadeiro extends Sobremesa{
}

fact{

all disj c1,c2: Cliente | c1.pedido != c2.pedido
}


pred show() {
#pedido = 3
}

run show for 3
