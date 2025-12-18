restriction Equality:
  "All x y #i. Eq(x,y) @i ==> x = y"

restriction Unique_User:
  "All user key1 key2 #i #j.
    UserCreated(user, key1) @i & UserCreated(user, key2) @j ==> #i = #j"

restriction Unique_Init_Response:
  "All node user #i #j.
    Finished(node, user) @i & Finished(node, user) @j ==> #i = #j"

restriction XOR_Node_Processing:
  "All user #i #j.
    PathA_Request(user) @i & PathB_Request(user) @j ==> F"

rule Init_NodeInit:
    [
        Fr(~ltkNodeInit)
    ]
    -->
    [
        !Ltk($NodeInit, ~ltkNodeInit),
        !Pk($NodeInit, pk(~ltkNodeInit)),
        Out(pk(~ltkNodeInit))
    ]

rule Init_User:
    [
        Fr(~ltkUser)
    ]
    --[ UserCreated($User, ~ltkUser) ]->
    [
        !Ltk($User, ~ltkUser)
    ]

rule Init_User_Request:
    [
        !Ltk($User, ~ltkUser),
        !Pk($NodeInit, pkNodeInit),
        Fr(~init_vc),
        Fr(~init_message),
        Fr(~n)
    ]
    -->
    [
        Out(aenc(<$User, pk(~ltkUser), ~init_vc, ~init_message, ~n>, pkNodeInit)),
        State($User, <$NodeInit, 'request', ~init_vc, ~init_message, ~n>)
    ]

rule NodeInit_Process:
    let
        payload = <~reply_init_vc, ~post_init_vc_location, h(nonce)>
        signature = sign(payload, ~ltkNodeInit)
    in
    [
        In( aenc(<User, receivedKey, init_vc, init_message, nonce>, pk(~ltkNodeInit)) ),
        !Ltk($NodeInit, ~ltkNodeInit),
        Fr(~reply_init_vc),
        Fr(~post_init_vc_location)
    ]
    --[ Finished($NodeInit, User) ]->
    [
        !LearnedKeysNodeInit($NodeInit, <User, receivedKey>),
        Out(aenc(<payload, signature>, receivedKey)),
        State($NodeInit, <User, 'init'>)
    ]

rule User_Branching:
    let
        payload = <reply_init_vc, post_init_vc_location, received_hash>
    in
    [
        In( aenc(<payload, signature>, pk(~ltkUser)) ),
        State($User, <$NodeInit, 'request', init_vc, init_message, n>),
        !Ltk($User, ~ltkUser),
        !Pk($NodeInit, pkNodeInit)
    ]
    --[
        Eq(received_hash, h(n)),
        Eq(verify(signature, payload, pkNodeInit), true),
        User_Passes_Initialization($User, reply_init_vc, post_init_vc_location)
    ]->
    [
        State($User, <$NodeInit, 'response', reply_init_vc, post_init_vc_location>)
    ]

lemma User_Key_Secretary:
    "All user key #i.
        UserCreated(user, key) @i
        ==>
        not (Ex #j. K(key) @j)"

lemma Functional_Test:
    exists-trace
    "Ex node user #i.
        Finished(node, user) @i"

lemma User_Receives_Response:
    "All user reply_vc loc #i.
        User_Passes_Initialization(user, reply_vc, loc) @i
        ==>
        ( not (Ex #j. K(reply_vc) @j) )
        &
        ( not (Ex #k. K(loc) @k) )"