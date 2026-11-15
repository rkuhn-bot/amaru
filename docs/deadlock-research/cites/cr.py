import json,sys,urllib.parse,urllib.request
q=sys.argv[1]; n=int(sys.argv[2]) if len(sys.argv)>2 else 3
u="https://api.crossref.org/works?rows=%d&select=DOI,title,author,container-title,issued,type&query.bibliographic=%s"%(n,urllib.parse.quote(q))
req=urllib.request.Request(u,headers={"User-Agent":"research (mailto:none@example.com)"})
d=json.load(urllib.request.urlopen(req,timeout=30))
for it in d["message"]["items"]:
  a=", ".join((x.get("family","") ) for x in it.get("author",[])[:6])
  print("-",a,"|",(it.get("title") or [""])[0],"|",(it.get("container-title") or [""])[0],it["issued"]["date-parts"][0][0] if it.get("issued",{}).get("date-parts") else "","| https://doi.org/"+it["DOI"])
