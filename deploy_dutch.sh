ft multisig -a user1 --transfer 5 --to AuctionRoot deployDutchAuction '{"root_wallet":"%{account:address:CrystalRootWallet}", "winner_processor":"%{account:address:CrystalProcessWinner}", "start_price":"1000", "end_price": "7", "price_delta": "10", "time_delta": 2}' &&

dests=ft inspect --past AuctionRoot 2>&1 | grep '\"dst\":' | sed -e 's/"dst": "//g' | sed -e 's/ (.*",//g' | sed -e 's/",//g' | sed -e 's/ //g'

echo "Auction = $dests[-1], BidBuilder = $dests[-2]"
