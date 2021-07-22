
all: contracts
	ft contract import OCP_AutomaticDutchAuction.tvm -f
	ft contract import OCP_AutomaticDutchAuctionSetcode.tvm -f
	ft contract import OCP_ManualDutchAuction.tvm -f
	ft contract import OCP_ManualDutchAuctionSetcode.tvm -f
	ft contract import OCP_EnglishAuction.tvm -f
	ft contract import OCP_EnglishAuctionSetcode.tvm -f

contracts:: OCP_AutomaticDutchAuction.tvm

OCP_AutomaticDutchAuction.tvm: *.spp
	ft contract build -f OCP_AutomaticDutchAuction.spp --contract OCP_AutomaticDutchAuction

contracts:: OCP_AutomaticDutchAuctionSetcode.tvm

OCP_AutomaticDutchAuctionSetcode.tvm: *.spp
	ft contract build -f OCP_AutomaticDutchAuctionSetcode.spp --contract OCP_AutomaticDutchAuctionSetcode

contracts:: OCP_ManualDutchAuction.tvm

OCP_ManualDutchAuction.tvm: *.spp
	ft contract build -f OCP_ManualDutchAuction.spp --contract OCP_ManualDutchAuction

contracts:: OCP_ManualDutchAuctionSetcode.tvm

OCP_ManualDutchAuctionSetcode.tvm: *.spp
	ft contract build -f OCP_ManualDutchAuctionSetcode.spp --contract OCP_ManualDutchAuctionSetcode

contracts:: OCP_EnglishAuctionSetcode.tvm

OCP_EnglishAuctionSetcode.tvm: *.spp
	ft contract build -f OCP_EnglishAuctionSetcode.spp --contract OCP_EnglishAuctionSetcode

contracts:: OCP_EnglishAuction.tvm

OCP_EnglishAuction.tvm: *.spp
	ln -sf OCP_DirectAuctions.spp OCP_EnglishAuction.spp
	ft contract build -f OCP_EnglishAuction.spp --contract OCP_EnglishAuction

clean:
	rm -f *~ *.sol *.tvm *.abi.json *.code

