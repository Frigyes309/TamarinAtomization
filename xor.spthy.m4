theory XOR_process
begin

builtins: hashing, asymmetric-encryption, signing

include(`./raw/init.spthy.raw')
// ')

rule NodeA_Setup:
    [ Fr(~ltkNodeA) ]
    -->
    [ !Ltk($NodeA, ~ltkNodeA), !Pk($NodeA, pk(~ltkNodeA)), Out(pk(~ltkNodeA)) ]

rule NodeB_Setup:
    [ Fr(~ltkNodeB) ]
    -->
    [ !Ltk($NodeB, ~ltkNodeB), !Pk($NodeB, pk(~ltkNodeB)), Out(pk(~ltkNodeB)) ]

rule PathA_Request:
    [
        !Ltk($User, ~ltkUser),
        !Pk($NodeA, pkNodeA),
        State($User, <$NodeInit, 'response', reply_init_vc, post_init_vc_location>),
        Fr(~n)
    ]
    -->
    [
        State($User, <$NodeA, 'request', reply_init_vc, post_init_vc_location, ~n>),
        Out(aenc(<$User, pk(~ltkUser), reply_init_vc, post_init_vc_location, ~n>, pkNodeA))
    ]

rule PathB_Request:
    [
        !Ltk($User, ~ltkUser),
        !Pk($NodeB, pkNodeB),
        State($User, <$NodeInit, 'response', reply_init_vc, post_init_vc_location>),
        Fr(~n)
    ]
    -->
    [
        State($User, <$NodeB, 'request', reply_init_vc, post_init_vc_location, ~n>),
        Out(aenc(<$User, pk(~ltkUser), reply_init_vc, post_init_vc_location, ~n>, pkNodeB))
    ]

rule NodeA_Process:
    let
        payload = <next_location, ~future_head, h(nonce)>
        signature = sign(payload, ~ltkNodeA)
    in
    [
        In( aenc(<User, receivedKey, current_snake, next_location, nonce>, pk(~ltkNodeA)) ),
        !Ltk($NodeA, ~ltkNodeA),
        Fr(~future_head)
    ]
    --[PathA_Request(User)]->
    [
        !LearnedKeysNodeA($NodeA, <User, receivedKey>),
        Out(aenc(<payload, signature>, receivedKey)),
        State($NodeA, <User, 'response'>)
    ]

rule NodeB_Process:
    let
        payload = <next_location, ~future_head, h(nonce)>
        signature = sign(payload, ~ltkNodeB)
    in
    [
        In( aenc(<User, receivedKey, current_snake, next_location, nonce>, pk(~ltkNodeB)) ),
        !Ltk($NodeB, ~ltkNodeB),
        Fr(~future_head)
    ]
    --[PathB_Request(User)]->
    [
        !LearnedKeysNodeB($NodeB, <User, receivedKey>),
        Out(aenc(<payload, signature>, receivedKey)),
        State($NodeB, <User, 'response'>)
    ]

rule User_XOR_Process_A:
    let
        payload = <current_vc, next_vc_location, received_hash>
    in
    [
        In( aenc(<payload, signature>, pk(~ltkUser)) ),
        !Ltk($User, ~ltkUser),
        State($User, <$NodeA, 'request', reply_init_vc, post_init_vc_location, n>),
        !Pk($NodeA, pkNodeA)
    ]
    --[
        Eq(received_hash, h(n)),
        Eq(verify(signature, payload, pkNodeA), true),
        UserPassesNodeA($User, current_vc, next_vc_location)
    ]->
    [
        State($User, <$NodeA, 'response', current_vc, next_vc_location>)
    ]

rule User_XOR_Process_B:
    let
        payload = <current_vc, next_vc_location, received_hash>
    in
    [
        In( aenc(<payload, signature>, pk(~ltkUser)) ),
        !Ltk($User, ~ltkUser),
        State($User, <$NodeB, 'request', reply_init_vc, post_init_vc_location, n>),
        !Pk($NodeB, pkNodeB)
    ]
    --[
        Eq(received_hash, h(n)),
        Eq(verify(signature, payload, pkNodeB), true),
        UserPassesNodeB($User, current_vc, next_vc_location)
    ]->
    [
        State($User, <$NodeB, 'response', current_vc, next_vc_location>)
    ]

lemma User_XOR_AB:
    "All user current_vc next_vc_location #i.
        UserPassesNodeA(user, current_vc, next_vc_location) @i
        ==>
        not (Ex #j. UserPassesNodeB(user, current_vc, next_vc_location) @j)"

lemma Non_ExUser_XOR_AB:
    exists-trace
    "All user current_vc next_vc_location #i.
        UserPassesNodeA(user, current_vc, next_vc_location) @i
        ==>
        Ex other_vc other_loc #j. UserPassesNodeB(user, other_vc, other_loc) @j"

lemma User_XOR_BA:
    "All user current_vc next_vc_location #i.
        UserPassesNodeB(user, current_vc, next_vc_location) @i
        ==>
        not (Ex #j. UserPassesNodeA(user, current_vc, next_vc_location) @j)"

lemma User_Got_ReponseA:
    exists-trace
    "Ex user a b #i.
        UserPassesNodeA(user, a, b) @i"

lemma User_Got_ReponseB:
    exists-trace
    "Ex user a b #i.
        UserPassesNodeB(user, a, b) @i"

lemma PathA_Key_Secretary:
    "All user vc next #i.
        UserPassesNodeA(user, vc, next) @i
        ==>
        (not (Ex #j. K(vc) @j))
        & (not (Ex #k. K(next) @k))"

lemma PathB_Key_Secretary:
    "All user vc next #i.
        UserPassesNodeB(user, vc, next) @i
        ==>
        (not (Ex #j. K(vc) @j))
        & (not (Ex #k. K(next) @k))"

end