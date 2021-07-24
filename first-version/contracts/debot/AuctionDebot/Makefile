all: build

build: AuctionDebot.tvm

AuctionDebot.tvm: AuctionDebot.sol lib/*.sol
	ft contract build AuctionDebot.sol -f

deploy:
	ft contract deploy AuctionDebot --create debot_Auction -f
	ft call debot_Auction setABI '{ "dabi": "%{hex:read:contract:abi:AuctionDebot}" }'
	ft call debot_Auction setIcon '{ "icon": "%{hex:string:data:image/png;base64,%{base64:file:AuctionDebot.png}}" }'

run:
	ft client -- debot fetch %{account:address:debot_Auction}

invoke:
	ft client -- debot invoke %{account:address:debot_Auction} '%{account:in-message:debot_Auction:0:other_entry:{ "x": 3 \}}'
