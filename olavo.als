module olavo

one sig Lanchonete {
	clientes : set Cliente
}

sig Cliente {
	pedidos : Pedido
}
