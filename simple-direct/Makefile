
all: contracts
	ft contract import OCP_AutomaticDutchAuction.tvm -f
	ft contract import OCP_AutomaticDutchAuctionSetcode.tvm -f
	ft contract import OCP_ManualDutchAuction.tvm -f
	ft contract import OCP_ManualDutchAuctionSetcode.tvm -f
	ft contract import OCP_EnglishAuction.tvm -f
	ft contract import OCP_EnglishAuctionSetcode.tvm -f
	ft contract import OCP_ReverseEnglishAuction.tvm -f

contracts:: OCP_AutomaticDutchAuction.tvm

OCP_AutomaticDutchAuction.tvm: OCP_DirectAuctions.spp OCP_AutomaticDutchAuction.spp
	ft contract build -f OCP_AutomaticDutchAuction.spp --contract OCP_AutomaticDutchAuction

contracts:: OCP_AutomaticDutchAuctionSetcode.tvm

OCP_AutomaticDutchAuctionSetcode.tvm: OCP_DirectAuctions.spp OCP_AutomaticDutchAuctionSetcode.spp
	ft contract build -f OCP_AutomaticDutchAuctionSetcode.spp --contract OCP_AutomaticDutchAuctionSetcode

contracts:: OCP_ManualDutchAuction.tvm

OCP_ManualDutchAuction.tvm: OCP_DirectAuctions.spp OCP_ManualDutchAuction.spp
	ft contract build -f OCP_ManualDutchAuction.spp --contract OCP_ManualDutchAuction

contracts:: OCP_ManualDutchAuctionSetcode.tvm

OCP_ManualDutchAuctionSetcode.tvm: OCP_DirectAuctions.spp OCP_ManualDutchAuctionSetcode.spp
	ft contract build -f OCP_ManualDutchAuctionSetcode.spp --contract OCP_ManualDutchAuctionSetcode

contracts:: OCP_EnglishAuctionSetcode.tvm

OCP_EnglishAuctionSetcode.tvm: OCP_DirectAuctions.spp OCP_EnglishAuctionSetcode.spp
	ft contract build -f OCP_EnglishAuctionSetcode.spp --contract OCP_EnglishAuctionSetcode

contracts:: OCP_EnglishAuction.tvm

OCP_EnglishAuction.tvm: OCP_DirectAuctions.spp OCP_EnglishAuction.spp
	ft contract build -f OCP_EnglishAuction.spp --contract OCP_EnglishAuction

contracts:: OCP_ReverseEnglishAuction.tvm

OCP_ReverseEnglishAuction.tvm: OCP_DirectAuctions.spp OCP_ReverseAuctions.spp OCP_ReverseEnglishAuction.spp OCP_AuctionBidder.hash
	ft contract build -f OCP_ReverseEnglishAuction.spp --contract OCP_ReverseEnglishAuction

contracts:: OCP_AuctionBidder.tvm

OCP_AuctionBidder.hash: OCP_AuctionBidder.tvm
	ft contract import -f OCP_AuctionBidder.tvm

OCP_AuctionBidder.tvm: OCP_DirectAuctions.spp OCP_ReverseAuctions.spp OCP_AuctionBidder.spp
	ft contract build -f OCP_AuctionBidder.spp --contract OCP_AuctionBidder


clean:
	rm -f *~ *.sol *.tvm *.abi.json *.code

