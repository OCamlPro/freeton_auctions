
all: 
	ft contract import --make contracts/OCP_AutomaticDutchAuction.spp -f
	ft contract import --make contracts/OCP_ManualDutchAuction.spp -f
	ft contract import --make contracts/OCP_EnglishAuction.spp -f
	ft contract import --make contracts/OCP_AuctionBidder.spp -f
	ft contract import --make contracts/OCP_ReverseEnglishAuction.spp -f --contract OCP_ReverseEnglishAuction

clean:
	rm -f *~ *.code *.tvm *.abi.json */*~ *.sol
