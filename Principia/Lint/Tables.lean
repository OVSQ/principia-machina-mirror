import Principia.CanonicalReader

/-!
# The prompt lint's tables: v1's own text

v1's `tpc_lint` 0.1.0 carries its tables as one JSON text written by
version 1's lint tables generator and embedded in both residences:
`KNOWN_KEYS` (the member names a locator may show), the negation table `NEG` with its
window `NEG_WINDOW` and sentence stops `NEG_STOP`, the credential shapes `PL2`, the phrase
tables `PL3`, `PL4`, `PL5`, `PL6`, `PL9`, the open-ended tool table `PL7` and the
character classes of `PL2`. `tablesJson` is that text, character for character as v1
wrote it (its `LINT_TABLES_JSON`); the lint tests check it against the text of
version 1's lint module. v1 checked the text against the SHA-256 it records
(`tablesSha256`) when it loaded it; the lint tests make that check with the Calculator's
SHA-256 (`Principia.Sha256`), beside the comparison with v1's text.

`tables` is the text read (`Principia.Canonical.readString`) into typed tables. The
tables are v1's data, read as v1 reads them; they are not rewritten in Lean.
-/

namespace Principia.Lint

/-- The tables' version, v1's `LINT_TABLES_VERSION`. -/
def tablesVersion : String := "0.1.0"

/-- The SHA-256 v1 records for `tablesJson`'s ASCII bytes (`LINT_TABLES_SHA256`). -/
def tablesSha256 : String := "7dbc052a0c9d5a752f267529343d9d5eaccd66500b88b859923858804a924c17"

/-- v1's `LINT_TABLES_JSON`, in pieces of 72 characters. -/
def tablesJson : String := String.join [
    "{\"KNOWN_KEYS\":[\"$defs\",\"$id\",\"$ref\",\"$schema\",\"_meta\",\"additionalPropert",
    "ies\",\"allOf\",\"annotations\",\"anyOf\",\"cache_control\",\"const\",\"contentEncod",
    "ing\",\"contentMediaType\",\"default\",\"definitions\",\"deprecated\",\"descriptio",
    "n\",\"destructiveHint\",\"enum\",\"examples\",\"exclusiveMaximum\",\"exclusiveMini",
    "mum\",\"format\",\"function\",\"idempotentHint\",\"inputSchema\",\"input_schema\",\"",
    "items\",\"maxItems\",\"maxLength\",\"maximum\",\"minItems\",\"minLength\",\"minimum\"",
    ",\"name\",\"not\",\"oneOf\",\"openWorldHint\",\"outputSchema\",\"output_schema\",\"pa",
    "rameters\",\"pattern\",\"patternProperties\",\"prefixItems\",\"properties\",\"read",
    "Only\",\"readOnlyHint\",\"required\",\"strict\",\"title\",\"type\",\"uniqueItems\",\"w",
    "riteOnly\"],\"NEG\":[\"not\",\"never\",\"no\",\"nor\",\"cannot\",\"dont\",\"don't\",\"don\\",
    "u2019t\",\"cant\",\"can't\",\"can\\u2019t\",\"mustnt\",\"mustn't\",\"mustn\\u2019t\",\"s",
    "houldnt\",\"shouldn't\",\"shouldn\\u2019t\",\"wont\",\"won't\",\"won\\u2019t\",\"doesn",
    "t\",\"doesn't\",\"doesn\\u2019t\"],\"NEG_STOP\":\".!?;:\",\"NEG_WINDOW\":4,\"PL2\":[[\"",
    "PL2-01\",[[[\"L\",\"akia\"],[\"C\",\"V\",16,16]]]],[\"PL2-02\",[[[\"L\",\"asia\"],[\"C\",",
    "\"V\",16,16]]]],[\"PL2-03\",[[[\"L\",\"ghp_\"],[\"C\",\"N\",36,36]]]],[\"PL2-04\",[[[\"",
    "L\",\"gho_\"],[\"C\",\"N\",36,36]]]],[\"PL2-05\",[[[\"L\",\"ghu_\"],[\"C\",\"N\",36,36]]]",
    "],[\"PL2-06\",[[[\"L\",\"ghs_\"],[\"C\",\"N\",36,36]]]],[\"PL2-07\",[[[\"L\",\"ghr_\"],[",
    "\"C\",\"N\",36,36]]]],[\"PL2-08\",[[[\"L\",\"github_pat_\"],[\"C\",\"W\",82,82]]]],[\"P",
    "L2-09\",[[[\"L\",\"glpat-\"],[\"C\",\"U\",20,20]]]],[\"PL2-10\",[[[\"L\",\"xox\"],[\"C\",",
    "\"X\",1,1],[\"L\",\"-\"],[\"C\",\"D\",10,12],[\"L\",\"-\"],[\"C\",\"D\",10,13],[\"L\",\"-\"],[",
    "\"C\",\"N\",24,26]]]],[\"PL2-11\",[[[\"L\",\"xapp-\"],[\"C\",\"U\",20,255]]]],[\"PL2-12",
    "\",[[[\"L\",\"aiza\"],[\"C\",\"U\",35,35]]]],[\"PL2-13\",[[[\"L\",\"sk_live_\"],[\"C\",\"N",
    "\",20,255]]]],[\"PL2-14\",[[[\"L\",\"rk_live_\"],[\"C\",\"N\",20,255]]]],[\"PL2-15\",",
    "[[[\"L\",\"sk_test_\"],[\"C\",\"N\",20,255]]]],[\"PL2-16\",[[[\"L\",\"sk-\"],[\"C\",\"N\",",
    "20,20],[\"L\",\"t3blbkfj\"],[\"C\",\"N\",20,20]]]],[\"PL2-17\",[[[\"L\",\"sk-proj-\"],",
    "[\"C\",\"U\",20,4096]]]],[\"PL2-18\",[[[\"L\",\"sk-svcacct-\"],[\"C\",\"U\",20,4096]]]",
    "],[\"PL2-19\",[[[\"L\",\"sk-admin-\"],[\"C\",\"U\",20,4096]]]],[\"PL2-20\",[[[\"L\",\"s",
    "k-ant-\"],[\"C\",\"U\",20,4096]]]],[\"PL2-21\",[[[\"L\",\"hf_\"],[\"C\",\"L\",34,34]]]]",
    ",[\"PL2-22\",[[[\"L\",\"npm_\"],[\"C\",\"N\",36,36]]]],[\"PL2-23\",[[[\"L\",\"pypi-agei",
    "chlwas5vcmc\"],[\"C\",\"U\",50,1000]]]],[\"PL2-24\",[[[\"L\",\"eyj\"],[\"C\",\"U\",10,4",
    "096],[\"L\",\".eyj\"],[\"C\",\"U\",10,4096],[\"L\",\".\"],[\"C\",\"U\",0,4096]]]],[\"PL2-",
    "25\",[[[\"L\",\"-----begin private key-----\"]],[[\"L\",\"-----begin encrypted p",
    "rivate key-----\"]],[[\"L\",\"-----begin rsa private key-----\"]],[[\"L\",\"----",
    "-begin dsa private key-----\"]],[[\"L\",\"-----begin ec private key-----\"]],",
    "[[\"L\",\"-----begin openssh private key-----\"]],[[\"L\",\"-----begin pgp priv",
    "ate key block-----\"]]]],[\"PL2-26\",[[[\"L\",\"bearer \"],[\"C\",\"K\",20,4096]]]]",
    ",[\"PL2-27\",[[[\"L\",\"authorization: basic \"],[\"C\",\"K\",8,4096]]]],[\"PL2-28\"",
    ",[[[\"L\",\"x-api-key:\"],[\"C\",\"S\",0,1],[\"C\",\"U\",16,4096]]]],[\"PL2-29\",[[[\"L",
    "\",\"://\"],[\"C\",\"I\",1,256],[\"L\",\":\"],[\"C\",\"I\",1,256],[\"L\",\"@\"]]]],[\"PL2-30",
    "\",[[[\"L\",\"password\"],[\"C\",\"S\",0,1],[\"C\",\"E\",1,1],[\"C\",\"S\",0,1],[\"C\",\"Q\",",
    "0,1],[\"C\",\"G\",8,4096]],[[\"L\",\"passwd\"],[\"C\",\"S\",0,1],[\"C\",\"E\",1,1],[\"C\",",
    "\"S\",0,1],[\"C\",\"Q\",0,1],[\"C\",\"G\",8,4096]],[[\"L\",\"api_key\"],[\"C\",\"S\",0,1],",
    "[\"C\",\"E\",1,1],[\"C\",\"S\",0,1],[\"C\",\"Q\",0,1],[\"C\",\"G\",8,4096]],[[\"L\",\"apike",
    "y\"],[\"C\",\"S\",0,1],[\"C\",\"E\",1,1],[\"C\",\"S\",0,1],[\"C\",\"Q\",0,1],[\"C\",\"G\",8,4",
    "096]],[[\"L\",\"api-key\"],[\"C\",\"S\",0,1],[\"C\",\"E\",1,1],[\"C\",\"S\",0,1],[\"C\",\"Q",
    "\",0,1],[\"C\",\"G\",8,4096]],[[\"L\",\"secret_key\"],[\"C\",\"S\",0,1],[\"C\",\"E\",1,1]",
    ",[\"C\",\"S\",0,1],[\"C\",\"Q\",0,1],[\"C\",\"G\",8,4096]],[[\"L\",\"client_secret\"],[\"",
    "C\",\"S\",0,1],[\"C\",\"E\",1,1],[\"C\",\"S\",0,1],[\"C\",\"Q\",0,1],[\"C\",\"G\",8,4096]],",
    "[[\"L\",\"access_token\"],[\"C\",\"S\",0,1],[\"C\",\"E\",1,1],[\"C\",\"S\",0,1],[\"C\",\"Q\"",
    ",0,1],[\"C\",\"G\",8,4096]],[[\"L\",\"auth_token\"],[\"C\",\"S\",0,1],[\"C\",\"E\",1,1],",
    "[\"C\",\"S\",0,1],[\"C\",\"Q\",0,1],[\"C\",\"G\",8,4096]],[[\"L\",\"private_key\"],[\"C\",",
    "\"S\",0,1],[\"C\",\"E\",1,1],[\"C\",\"S\",0,1],[\"C\",\"Q\",0,1],[\"C\",\"G\",8,4096]],[[\"",
    "L\",\"aws_secret_access_key\"],[\"C\",\"S\",0,1],[\"C\",\"E\",1,1],[\"C\",\"S\",0,1],[\"",
    "C\",\"Q\",0,1],[\"C\",\"G\",8,4096]]]]],\"PL3\":[[\"PL3-01\",[[[\"follow\",\"obey\",\"ex",
    "ecute\",\"carry out\",\"act on\"],[\" \"],[\"the \",\"any \",\"all \",\"\"],[\"instructi",
    "ons\",\"directions\",\"commands\",\"directives\",\"orders\"],[\" \"],[\"in\",\"from\",\"",
    "found in\",\"contained in\",\"embedded in\",\"inside\"],[\" \"],[\"tool results\",\"",
    "tool output\",\"tool outputs\",\"tool responses\",\"web pages\",\"wiki pages\",\"t",
    "he wiki\",\"retrieved content\",\"retrieved documents\",\"search results\",\"doc",
    "uments\",\"files\",\"emails\",\"other agents\",\"another agent\",\"the server\",\"th",
    "e api\",\"tpx\"]]]],[\"PL3-02\",[[[\"treat \"],[\"tool results\",\"tool output\",\"t",
    "ool outputs\",\"tool responses\",\"wiki content\",\"wiki pages\",\"the wiki\",\"re",
    "trieved content\",\"search results\",\"documents\",\"file contents\",\"emails\",\"",
    "messages from other agents\",\"server messages\",\"tpx responses\"],[\" as \"],",
    "[\"instructions\",\"commands\",\"authoritative\",\"authorization\",\"trusted\"]]]]",
    ",[\"PL3-03\",[[[\"you are\",\"you're\",\"you have been\"],[\" \"],[\"authorized\",\"a",
    "uthorised\",\"permitted\",\"allowed\",\"cleared\",\"pre-authorized\",\"preauthoriz",
    "ed\"],[\" to\"]]]],[\"PL3-04\",[[[\"you have\",\"i give you\",\"i grant you\",\"you ",
    "are granted\",\"you have been granted\"],[\" \"],[\"my \",\"full \",\"standing \",\"",
    "blanket \",\"\"],[\"permission\",\"authorization\",\"authorisation\",\"approval\",\"",
    "consent\"],[\" to\"]]]],[\"PL3-05\",[[[\"consider\",\"treat\"],[\" \"],[\"it\",\"this\"",
    ",\"that\",\"all actions\",\"every action\",\"such actions\",\"these actions\"],[\" ",
    "\"],[\"as \",\"\"],[\"approved\",\"authorized\",\"authorised\",\"pre-approved\",\"prea",
    "pproved\",\"sanctioned\"]]]],[\"PL3-06\",[[[\"assume\",\"presume\"],[\" \"],[\"the u",
    "ser's \",\"the human's \",\"the sponsor's \",\"the operator's \",\"my \",\"\"],[\"ap",
    "proval\",\"consent\",\"permission\",\"authorization\",\"authorisation\"]]]],[\"PL3",
    "-07\",[[[\"pre-approved\",\"preapproved\",\"approved in advance\",\"authorized i",
    "n advance\",\"authorised in advance\"]]]],[\"PL3-08\",[[[\"no need to\",\"do not",
    " need to\",\"don't need to\",\"you need not\"],[\" \"],[\"ask\",\"wait for\",\"reque",
    "st\",\"seek\",\"obtain\",\"get\"],[\" \"],[\"for \",\"\"],[\"permission\",\"approval\",\"c",
    "onfirmation\",\"consent\",\"authorization\",\"authorisation\"]]]],[\"PL3-09\",[[[",
    "\"without \"],[\"asking\",\"waiting for\",\"requesting\",\"seeking\"],[\" \"],[\"the ",
    "human\",\"the user\",\"the sponsor\",\"anyone\",\"permission\",\"approval\",\"confir",
    "mation\",\"consent\"]]]],[\"PL3-10\",[[[\"act\",\"proceed\",\"decide\"],[\" \"],[\"on ",
    "your own authority\",\"autonomously\",\"without supervision\"]]]],[\"PL3-11\",[",
    "[[\"on behalf of\",\"in the name of\"],[\" the \"],[\"sponsor\",\"user\",\"human\",\"",
    "operator\",\"declaring authority\"]]]],[\"PL3-12\",[[[\"your\",\"these\",\"the\"],[",
    "\" \"],[\"instructions\",\"rules\"],[\" \"],[\"override\",\"outrank\",\"supersede\",\"t",
    "ake precedence over\"],[\" \"],[\"the human\",\"the user\",\"any human\",\"the hum",
    "an's\",\"the user's\"]]]]],\"PL4\":[[\"PL4-01\",[[[\"ignore\",\"disregard\",\"forget",
    "\",\"override\",\"bypass\",\"set aside\"],[\" \"],[\"all \",\"any \",\"\"],[\"the \",\"you",
    "r \",\"\"],[\"previous\",\"prior\",\"above\",\"earlier\",\"preceding\",\"original\",\"sy",
    "stem\",\"other\"],[\" \"],[\"instructions\",\"instruction\",\"rules\",\"guidelines\",",
    "\"directives\",\"prompt\",\"prompts\",\"constraints\"]]]],[\"PL4-02\",[[[\"ignore\",",
    "\"disregard\",\"override\",\"bypass\",\"set aside\",\"relax\",\"suspend\",\"waive\"],[",
    "\" \"],[\"the \",\"any \",\"all \",\"\"],[\"tps\",\"agent contract\",\"contract\",\"speci",
    "fication\",\"gtp\",\"rules\",\"safety rules\",\"input vetting\",\"decision protoco",
    "l\",\"digest gate\",\"text safety rule\"]]]],[\"PL4-03\",[[[\"skip\",\"bypass\",\"om",
    "it\",\"circumvent\"],[\" \"],[\"the \",\"any \",\"all \",\"\"],[\"digest\",\"digests\",\"d",
    "igest gate\",\"digest check\",\"checks\",\"check\",\"verification\",\"validation\",",
    "\"gate\",\"lock\",\"mutex\",\"refusal\",\"refusals\",\"audit\",\"review\",\"quarantine\"",
    ",\"benchmark quarantine\",\"decision item\",\"decision items\",\"report\",\"repor",
    "ting\"]]]],[\"PL4-04\",[[[\"do not\",\"don't\",\"never\",\"no need to\"],[\" \"],[\"re",
    "port\",\"flag\",\"log\",\"record\",\"disclose\",\"mention\"],[\" \"],[\"it\",\"this\",\"th",
    "em\",\"detections\",\"injections\",\"probes\",\"canaries\",\"failures\",\"errors\",\"r",
    "efusals\",\"the detection\",\"the injection\",\"suspicious input\",\"suspect inp",
    "ut\"]]]],[\"PL4-05\",[[[\"always comply\",\"comply with every\",\"comply with al",
    "l\",\"comply with any\",\"never refuse\",\"do not refuse\",\"don't refuse\",\"neve",
    "r decline\",\"do not decline\",\"don't decline\"]]]],[\"PL4-06\",[[[\"compute\",\"",
    "calculate\",\"estimate\",\"guess\",\"reason\",\"work out\",\"approximate\"],[\" \"],[",
    "\"the \",\"a \",\"any \",\"\"],[\"digest\",\"digests\",\"hash\",\"hashes\",\"sha-256\",\"d(",
    "is)\",\"d(prompt)\",\"d(tfk)\"],[\" \"],[\"by hand\",\"by reasoning\",\"mentally\",\"i",
    "n your head\",\"without tpc\",\"without running tpc-py\",\"without executing t",
    "pc-py\"]]]],[\"PL4-07\",[[[\"identify\",\"detect\",\"spot\",\"recognize\",\"recognis",
    "e\",\"distinguish\",\"guess\",\"figure out\"],[\" \"],[\"the \",\"a \",\"any \",\"all \",",
    "\"\"],[\"probe\",\"probes\",\"canary\",\"canaries\",\"parrot\",\"parrots\",\"test input",
    "\",\"test inputs\",\"planted test\",\"planted tests\",\"planted error\",\"planted ",
    "errors\"]]]],[\"PL4-08\",[[[\"if \"],[\"this\",\"it\",\"the input\",\"the task\",\"the",
    " request\",\"the package\",\"the block\"],[\" \"],[\"is\",\"looks like\",\"seems lik",
    "e\",\"seems to be\",\"might be\",\"may be\",\"could be\",\"appears to be\"],[\" \"],[",
    "\"a \",\"an \",\"\"],[\"probe\",\"canary\",\"parrot\",\"test\",\"evaluation\",\"planted t",
    "est\"]]]],[\"PL4-09\",[[[\"when\",\"if\",\"while\",\"whenever\"],[\" you \"],[\"are\",\"",
    "suspect you are\",\"think you are\",\"believe you are\"],[\" \"],[\"being tested",
    "\",\"being evaluated\",\"being probed\",\"under evaluation\",\"tested\",\"evaluate",
    "d\",\"probed\"]]]],[\"PL4-10\",[[[\"treat\",\"handle\",\"answer\",\"respond to\"],[\" ",
    "\"],[\"probes\",\"canaries\",\"parrots\",\"tests\",\"test inputs\",\"suspected probe",
    "s\"],[\" \"],[\"differently\",\"with extra care\",\"more carefully\",\"specially\"]",
    "]]],[\"PL4-11\",[[[\"look up\",\"search for\",\"fetch\",\"read\",\"consult\",\"check\"",
    "],[\" the \"],[\"known\",\"expected\",\"published\",\"reference\",\"benchmark\",\"cor",
    "rect\"],[\" \"],[\"value\",\"values\",\"answer\",\"answers\",\"result\",\"results\"],[\"",
    " \"],[\"first\",\"before deriving\",\"before the derivation\",\"before you deriv",
    "e\"]]]]],\"PL5\":[[\"PL5-01\",[[[\"| class: instruction artifact\"]]]],[\"PL5-02",
    "\",[[[\"end of artifact --- tps\"]]]],[\"PL5-03\",[[[\"end of artifact --- gtp",
    "\"]]]],[\"PL5-04\",[[[\"the principia machina specification (tps)\"]]]],[\"PL5",
    "-05\",[[[\"the generic tps prompt (gtp)\"]]]],[\"PL5-06\",[[[\"tps\",\"gtp\"],[\" ",
    "version:\"]]]],[\"PL5-07\",[[[\"this part, taken as a runnable instruction s",
    "et, is gtp\"]]]],[\"PL5-08\",[[[\"part 6 agent contract\"]]]],[\"PL5-09\",[[[\"r",
    "eading conventions, for this file\"]]]]],\"PL6\":[[\"PL6-01\",[[[\"<important>",
    "\",\"</important>\",\"<instructions>\",\"</instructions>\",\"<instruction>\",\"<sy",
    "stem>\",\"</system>\",\"<system-reminder>\",\"[system]\",\"[inst]\",\"<<sys>>\",\"<|",
    "im_start|>\"]]]],[\"PL6-02\",[[[\"ignore\",\"disregard\",\"forget\",\"override\"],[",
    "\" \"],[\"all \",\"any \",\"\"],[\"the \",\"your \",\"\"],[\"previous\",\"prior\",\"above\",",
    "\"earlier\",\"preceding\",\"original\",\"system\",\"other\"],[\" \"],[\"instructions\"",
    ",\"instruction\",\"rules\",\"guidelines\",\"directives\",\"prompt\",\"prompts\"]]]],",
    "[\"PL6-03\",[[[\"do not\",\"don't\",\"never\"],[\" \"],[\"tell\",\"inform\",\"notify\",\"",
    "alert\",\"mention\",\"reveal\",\"show\",\"disclose\",\"say\"],[\" \"],[\"this \",\"it \",",
    "\"anything \",\"\"],[\"to \",\"\"],[\"the user\",\"the human\",\"the sponsor\",\"anyone",
    "\",\"that you\",\"this\"]]]],[\"PL6-04\",[[[\"without \"],[\"telling\",\"informing\",",
    "\"notifying\",\"alerting\"],[\" \"],[\"the user\",\"the human\",\"the sponsor\",\"any",
    "one\"]]]],[\"PL6-05\",[[[\"keep\",\"hide\"],[\" \"],[\"this\",\"it\"],[\" \"],[\"secret\"",
    ",\"hidden\",\"from the user\",\"from the human\"]]]],[\"PL6-06\",[[[\"the user \"]",
    ",[\"must not\",\"should not\",\"must never\",\"should never\"],[\" \"],[\"know\",\"se",
    "e\",\"find out\",\"be told\"]]]],[\"PL6-07\",[[[\"before\",\"prior to\"],[\" \"],[\"us",
    "ing\",\"calling\",\"invoking\",\"running\"],[\" \"],[\"this\",\"any\",\"any other\",\"an",
    "other\",\"the other\"],[\" tool\"]]]],[\"PL6-08\",[[[\"always\",\"first\"],[\" \"],[\"",
    "call\",\"use\",\"invoke\",\"run\"],[\" this tool\"]]]],[\"PL6-09\",[[[\"all other to",
    "ols\",\"any other tool\",\"every other tool\",\"the other tools\"]]]],[\"PL6-10\"",
    ",[[[\"instead of\",\"rather than\"],[\" \"],[\"using\",\"calling\",\"invoking\"],[\" ",
    "\"],[\"the\",\"any\",\"another\"]]]],[\"PL6-11\",[[[\"~/\",\"id_rsa\",\"id_ed25519\",\"i",
    "d_ecdsa\",\".ssh/\",\"mcp.json\",\".env\",\"/etc/passwd\",\"/etc/shadow\",\".aws/cre",
    "dentials\",\".netrc\",\".git-credentials\",\".npmrc\",\".pypirc\",\"credentials.js",
    "on\",\".kube/config\",\".docker/config.json\"]]]],[\"PL6-12\",[[[\"pass\",\"send\",",
    "\"include\",\"attach\",\"forward\",\"append\",\"upload\",\"post\"],[\" \"],[\"its\",\"the",
    "\",\"their\",\"all\",\"the file's\",\"the file\",\"those\",\"these\"],[\" \"],[\"content",
    "\",\"contents\"]]]],[\"PL6-13\",[[[\"read\",\"open\",\"cat\",\"load\",\"access\"],[\" \"]",
    ",[\"the \",\"\"],[\"private key\",\"ssh key\",\"ssh keys\",\"credentials\",\"secrets\"",
    ",\"environment variables\",\"config file\",\"configuration file\",\"api key\",\"a",
    "pi keys\",\"tokens\"]]]],[\"PL6-14\",[[[\"http://\",\"https://\",\"ftp://\",\"ngrok\"",
    ",\"pastebin\",\"requestbin\",\"webhook.site\",\"exfiltrate\",\"exfiltration\"]]]],",
    "[\"PL6-15\",[[[\"send\",\"post\",\"upload\",\"forward\",\"email\",\"transmit\"],[\" \"],",
    "[\"it\",\"them\",\"this\",\"the result\",\"the results\",\"the data\",\"everything\",\"",
    "all data\"],[\" to\"]]]],[\"PL6-16\",[[[\"add\",\"write\",\"save\",\"append\"],[\" \"],",
    "[\"this\",\"these instructions\",\"the following\"],[\" to \"],[\"memory\",\"your m",
    "emory\",\"claude.md\",\"agents.md\",\"your instructions\",\"the system prompt\"]]",
    "]]],\"PL7\":[[\"PL7-01\",[[\"bash\"],[\"sh\"],[\"zsh\"],[\"shell\"],[\"powershell\"],[",
    "\"pwsh\"],[\"cmd\"],[\"terminal\"],[\"subprocess\"],[\"exec\"],[\"execute\"],[\"eval\"",
    "],[\"repl\"],[\"run\",\"command\"],[\"run\",\"commands\"],[\"run\",\"code\"],[\"code\",\"",
    "interpreter\"],[\"run\",\"script\"],[\"run\",\"python\"]],[[[\"arbitrary\",\"any\",\"s",
    "hell\",\"bash\",\"terminal\",\"system\"],[\" \"],[\"command\",\"commands\"]],[[\"execu",
    "te\",\"executes\",\"run\",\"runs\",\"evaluate\",\"evaluates\"],[\" \"],[\"arbitrary \",",
    "\"any \",\"\"],[\"code\",\"python\",\"javascript\",\"scripts\",\"a script\",\"shell com",
    "mands\",\"a shell command\",\"a command\",\"commands\"]]]],[\"PL7-02\",[[\"fetch\"]",
    ",[\"webfetch\"],[\"curl\"],[\"wget\"],[\"browse\"],[\"browser\"],[\"navigate\"],[\"pu",
    "ppeteer\"],[\"playwright\"],[\"scrape\"],[\"scraper\"],[\"crawl\"],[\"crawler\"],[\"",
    "download\"],[\"http\",\"request\"],[\"http\",\"get\"],[\"http\",\"post\"],[\"url\",\"fet",
    "ch\"],[\"fetch\",\"url\"],[\"open\",\"url\"],[\"get\",\"url\"],[\"web\",\"request\"]],[[[",
    "\"any\",\"arbitrary\"],[\" \"],[\"url\",\"urls\",\"web page\",\"web pages\",\"website\",",
    "\"websites\",\"host\",\"hosts\"]],[[\"fetch\",\"fetches\",\"retrieve\",\"retrieves\",\"",
    "download\",\"downloads\",\"get\",\"gets\"],[\" \"],[\"a\",\"any\",\"the content of a\",",
    "\"the contents of a\",\"content from a\",\"content from any\"],[\" \"],[\"url\",\"w",
    "eb page\",\"website\"]]]],[\"PL7-03\",[[\"send\"],[\"email\"],[\"mail\"],[\"gmail\"],",
    "[\"smtp\"],[\"sms\"],[\"webhook\"],[\"tweet\"],[\"upload\"],[\"post\",\"message\"],[\"p",
    "ost\",\"to\"]],[[[\"send\",\"sends\"],[\" \"],[\"an \",\"a \",\"\"],[\"email\",\"emails\",\"",
    "message\",\"messages\",\"sms\",\"text message\",\"notification\"]],[[\"post\",\"post",
    "s\"],[\" \"],[\"a \",\"\"],[\"message\",\"messages\",\"tweet\",\"tweets\"],[\" to\"]]]]],",
    "\"PL9\":[[\"PL9-01\",[[[\"remember\",\"memorize\",\"memorise\",\"save\",\"store\",\"per",
    "sist\",\"record\",\"retain\",\"keep\"],[\" \"],[\"this\",\"these\",\"the following\",\"t",
    "hese instructions\",\"this instruction\",\"these rules\",\"this rule\",\"it\"],[\"",
    " \"],[\"for\",\"in\",\"across\",\"into\",\"to\"],[\" \"],[\"future\",\"later\",\"all futur",
    "e\",\"subsequent\",\"every\",\"your\",\"the\",\"long-term\",\"persistent\"],[\" \"],[\"s",
    "essions\",\"session\",\"conversations\",\"conversation\",\"memory\",\"runs\",\"work\"",
    "]]]],[\"PL9-02\",[[[\"write\",\"save\",\"store\",\"add\",\"append\",\"commit\"],[\" \"],",
    "[\"this\",\"these\",\"it\",\"them\",\"the following\",\"these instructions\",\"this i",
    "nstruction\",\"these rules\",\"a note\",\"notes\"],[\" \"],[\"to\",\"in\",\"into\"],[\" ",
    "\"],[\"memory\",\"your memory\",\"the memory\",\"long-term memory\",\"persistent m",
    "emory\",\"the memory file\",\"a memory file\",\"your memory file\",\"the knowled",
    "ge base\"]]]],[\"PL9-03\",[[[\"update\",\"edit\",\"modify\",\"rewrite\",\"change\",\"o",
    "verwrite\",\"extend\",\"amend\",\"append to\"],[\" \"],[\"your\",\"the\",\"this\"],[\" \"",
    "],[\"memory\",\"memories\",\"instructions\",\"system prompt\",\"prompt\",\"instruct",
    "ion file\",\"instruction files\",\"rules file\"]]]],[\"PL9-04\",[[[\"claude.md\",",
    "\"agents.md\",\"gemini.md\",\".cursorrules\",\".windsurfrules\",\".clinerules\",\"c",
    "opilot-instructions.md\",\".cursor/rules\",\".github/instructions\",\"memory.m",
    "d\",\".claude/\"]]]],[\"PL9-05\",[[[\"for\",\"in\",\"across\",\"during\"],[\" \"],[\"fut",
    "ure\",\"all future\",\"later\",\"subsequent\",\"every future\",\"next\"],[\" \"],[\"se",
    "ssions\",\"session\",\"conversations\",\"conversation\",\"runs\",\"chats\"]]]],[\"PL",
    "9-06\",[[[\"memory tool\",\"save_memory\",\"memory_write\",\"add_memory\",\"create",
    "_memory\",\"remember tool\"]]]]],\"classes\":{\"D\":\"0123456789\",\"E\":\"=:\",\"G\":\"",
    "!#$%&()*+,-./0123456789:;<=>?@[\\\\]^_abcdefghijklmnopqrstuvwxyz{|}~\",\"I\":",
    "\"abcdefghijklmnopqrstuvwxyz0123456789-._~%!$&'()*+,;=\",\"K\":\"abcdefghijkl",
    "mnopqrstuvwxyz0123456789-._~+/=\",\"L\":\"abcdefghijklmnopqrstuvwxyz\",\"N\":\"a",
    "bcdefghijklmnopqrstuvwxyz0123456789\",\"Q\":\"\\\"'`\",\"S\":\" \",\"U\":\"abcdefghijk",
    "lmnopqrstuvwxyz0123456789_-\",\"V\":\"abcdefghijklmnopqrstuvwxyz234567\",\"W\":",
    "\"abcdefghijklmnopqrstuvwxyz0123456789_\",\"X\":\"abprs\"},\"version\":\"0.1.0\"}",
  ]

/-! ## The typed tables -/

/-- One element of a credential shape (PL2): a literal, or a run of a class's characters,
between `lo` and `hi` long, taken possessively. -/
inductive Element where
  /-- `["L", text]` -/
  | lit (text : List Char)
  /-- `["C", class, lo, hi]`, the class given by its characters. -/
  | cls (chars : List Char) (lo hi : Nat)
  deriving Repr, Inhabited

/-- A phrase template: its parts, each a list of alternatives; a phrase is one
alternative of each part, in order. -/
abbrev Template := List (List (List Char))

/-- A table entry: its id (`PL3-01` ...) and its rules. -/
structure Entry (α : Type) where
  /-- The entry's id, the finding's item. -/
  id : String
  /-- The entry's patterns or templates. -/
  rules : List α
  deriving Repr, Inhabited

/-- A PL7 entry: its id, the token sequences a tool's name is searched for, and the
templates its description is searched for. -/
structure ToolEntry where
  /-- The entry's id. -/
  id : String
  /-- Token sequences of a name. -/
  seqs : List (List String)
  /-- Templates of a description. -/
  templates : List Template
  deriving Repr, Inhabited

/-- The tables, typed. -/
structure Tables where
  /-- `KNOWN_KEYS` -/
  knownKeys : List String
  /-- `NEG` -/
  neg : List String
  /-- `NEG_STOP` -/
  negStop : List Char
  /-- `NEG_WINDOW` -/
  negWindow : Nat
  /-- `PL2`: credential shapes. -/
  pl2 : List (Entry (List Element))
  /-- `PL3`: a source of authorization other than the human. -/
  pl3 : List (Entry Template)
  /-- `PL4`: relaxation or probe-spotting. -/
  pl4 : List (Entry Template)
  /-- `PL5`: a second TPS or GTP text. -/
  pl5 : List (Entry Template)
  /-- `PL6`: tool text addressed to the model. -/
  pl6 : List (Entry Template)
  /-- `PL7`: open-ended tools. -/
  pl7 : List ToolEntry
  /-- `PL9`: persisting, memory and instruction files. -/
  pl9 : List (Entry Template)
  /-- The tables' own version. -/
  version : String
  deriving Repr, Inhabited

/-! ## Reading the text -/

open Principia.Canonical (Value)

/-- A list. -/
def asList : Value → Option (List Value)
  | .arr xs => some xs
  | _ => none

/-- A text. -/
def asText : Value → Option String
  | .str s => some s
  | _ => none

/-- A natural number. -/
def asNat : Value → Option Nat
  | .int n => if n ≥ 0 then some n.toNat else none
  | _ => none

/-- A list of texts. -/
def asTexts (v : Value) : Option (List String) := (asList v).bind (·.mapM asText)

/-- An object's member. -/
def member (v : Value) (k : String) : Option Value :=
  match v with
  | .obj ms => ms.lookup k
  | _ => none

/-- A template: a list of parts, each a list of alternatives. -/
def readTemplate (v : Value) : Option Template :=
  (asList v).bind (·.mapM fun part => (asTexts part).map (·.map String.toList))

/-- A phrase entry, `[id, [template, ...]]`. -/
def readPhraseEntry (v : Value) : Option (Entry Template) :=
  match asList v with
  | some [id, temps] => do
    pure ⟨← asText id, ← (← asList temps).mapM readTemplate⟩
  | _ => none

/-- A credential shape's element, its class resolved through `classes`. -/
def readElement (classes : List (String × String)) (v : Value) : Option Element :=
  match asList v with
  | some [k, t] => do
    guard ((← asText k) == "L")
    pure (.lit (← asText t).toList)
  | some [k, c, lo, hi] => do
    guard ((← asText k) == "C")
    let chars ← classes.lookup (← asText c)
    pure (.cls chars.toList (← asNat lo) (← asNat hi))
  | _ => none

/-- A PL2 entry, `[id, [[element, ...], ...]]`. -/
def readShapeEntry (classes : List (String × String)) (v : Value) : Option (Entry (List Element)) :=
  match asList v with
  | some [id, pats] => do
    pure ⟨← asText id, ← (← asList pats).mapM fun p => (asList p).bind (·.mapM (readElement classes))⟩
  | _ => none

/-- A PL7 entry, `[id, [sequence, ...], [template, ...]]`. -/
def readToolEntry (v : Value) : Option ToolEntry :=
  match asList v with
  | some [id, seqs, temps] => do
    pure ⟨← asText id, ← (← asList seqs).mapM asTexts, ← (← asList temps).mapM readTemplate⟩
  | _ => none

/-- The classes, `{letter: characters}`. -/
def readClasses : Value → Option (List (String × String))
  | .obj ms => ms.mapM fun (k, v) => do pure (k, ← asText v)
  | _ => none

/-- The text read into typed tables; `none` when any part does not read. -/
def readTables (text : String) : Option Tables := do
  let v ← (Principia.Canonical.readString text).toOption
  let classes ← readClasses (← member v "classes")
  let phrases (k : String) : Option (List (Entry Template)) := do
    (← asList (← member v k)).mapM readPhraseEntry
  pure {
    knownKeys := ← asTexts (← member v "KNOWN_KEYS")
    neg := ← asTexts (← member v "NEG")
    negStop := (← asText (← member v "NEG_STOP")).toList
    negWindow := ← asNat (← member v "NEG_WINDOW")
    pl2 := ← (← asList (← member v "PL2")).mapM (readShapeEntry classes)
    pl3 := ← phrases "PL3"
    pl4 := ← phrases "PL4"
    pl5 := ← phrases "PL5"
    pl6 := ← phrases "PL6"
    pl7 := ← (← asList (← member v "PL7")).mapM readToolEntry
    pl9 := ← phrases "PL9"
    version := ← asText (← member v "version") }

/-- v1's tables, read once. Empty if the text did not read, which the lint tests
refuse. -/
def tables : Tables := (readTables tablesJson).getD default

end Principia.Lint
