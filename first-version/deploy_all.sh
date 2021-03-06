bash deploy.sh EnglishAuction &&
bash deploy.sh EnglishReverseAuction &&
bash deploy.sh DutchAuction &&
bash deploy.sh DutchReverseAuction &&
bash deploy.sh CrystalProcessWinner &&
bash deploy.sh CrystalRootWallet &&
bash deploy.sh CrystalVault &&
bash deploy.sh Bid &&
bash deploy.sh BlindBid &&
bash deploy.sh BidBuilder &&
bash deploy.sh AuctionRoot '{"bid_address":"%{account:address:Bid}","blind_bid_address":"%{account:address:BlindBid}"}' &&

ft multisig transfer 10 --from user1 --to AuctionRoot init '{"english_auction":"%{account:address:EnglishAuction}", "english_reverse_auction":"%{account:address:EnglishReverseAuction}" ,"dutch_auction":"%{account:address:DutchAuction}" ,"dutch_reverse_auction":"%{account:address:DutchReverseAuction}", "bid_builder":"%{account:address:BidBuilder}"}'
