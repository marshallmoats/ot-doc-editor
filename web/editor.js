(() => {
"use strict";
const editor = document.getElementById("editor");
const els = { undo: document.getElementById("undo"), redo: document.getElementById("redo"),
  kind: document.getElementById("kind"), rev: document.getElementById("rev"), status: document.getElementById("status") };
const roomName = new URLSearchParams(location.search).get("room") || "demo";
const clientId = crypto.randomUUID ? crypto.randomUUID() : "client-" + Math.random().toString(36).slice(2);
const collabStatus = document.getElementById("collab-status");
document.getElementById("room-name").textContent = roomName;
let client = null, state = null, lastPos = { block: 0, offset: 0 };
let composing = null, activeRequest = null, actionPending = false, requestCounts = new Map(), idleWaiters = [], drainWaiters = [];
const cp = s => Array.from(s).length;
const cpToIdx = (s, n) => { let i = 0; for (const ch of s) { if (!n--) break; i += ch.length; } return i; };
const idxToCp = (s, i) => cp(s.slice(0, i));
const cmp = (a,b) => a.block-b.block || a.offset-b.offset;
const blockLen = i => state && state.doc[i] ? cp(state.doc[i].text) : 0;
function showError(msg) {
  els.status.textContent = msg; els.status.style.display = "inline-block";
  setTimeout(() => { els.status.style.display = "none"; }, 4000);
}
function syncKind() { const b = state && state.doc[lastPos.block]; els.kind.value = b ? b.kind : "para"; }
function render() {
  if (!state) return;
  const frag = document.createDocumentFragment();
  state.doc.forEach((b,i) => {
    const el = document.createElement("div"); el.className = "block k-" + b.kind; el.dataset.i = String(i);
    if (!b.text) el.appendChild(document.createElement("br")); else el.appendChild(document.createTextNode(b.text));
    frag.appendChild(el);
  });
  editor.replaceChildren(frag);
  els.undo.disabled = !state.canUndo; els.redo.disabled = !state.canRedo;
  els.rev.textContent = "rev " + state.rev; syncKind();
}
function blockOf(node) {
  while (node && node !== editor) { if (node.parentNode === editor) return node; node = node.parentNode; }
  return null;
}
function domToPos(node, off) {
  if (!node) return null;
  if (node === editor) {
    const n = editor.children.length;
    if (!n) return {block:0,offset:0};
    if (off >= n) return {block:n-1,offset:blockLen(n-1)};
    return {block:off,offset:0};
  }
  const b = blockOf(node); if (!b) return null;
  const i = Number(b.dataset.i);
  if (node === b) return {block:i,offset:off === 0 ? 0 : blockLen(i)};
  if (node.nodeType === 3) return {block:i,offset:idxToCp(node.data,off)};
  return {block:i,offset:0};
}
function currentRange() {
  const sel = getSelection();
  if (sel && sel.rangeCount && editor.contains(sel.anchorNode)) {
    const a=domToPos(sel.anchorNode,sel.anchorOffset), f=domToPos(sel.focusNode,sel.focusOffset);
    if (a&&f) return cmp(a,f)<=0 ? {from:a,to:f} : {from:f,to:a};
  }
  return {from:lastPos,to:lastPos};
}
function pointFor(pos) {
  const b=Math.max(0,Math.min(pos.block,state.doc.length-1));
  const o=Math.max(0,Math.min(pos.offset,blockLen(b)));
  const el=editor.children[b], t=el.firstChild;
  return t && t.nodeType===3 ? [t,cpToIdx(t.data,o)] : [el,0];
}
function setRange(range) {
  if (!state || !state.doc.length) return;
  const a=pointFor(range.from), b=pointFor(range.to), r=document.createRange();
  r.setStart(a[0],a[1]);r.setEnd(b[0],b[1]);
  const sel=getSelection();sel.removeAllRanges();sel.addRange(r);
  lastPos={...range.to};syncKind();
}
function setCaret(pos) { setRange({from:pos,to:pos}); }
document.addEventListener("selectionchange", () => {
  const s=getSelection(); if (s&&s.rangeCount&&editor.contains(s.focusNode)) {
    const p=domToPos(s.focusNode,s.focusOffset); if(p){lastPos=p;syncKind();}
  }
});
function snapshotFromClient() {
  state = { doc: client.doc, rev: client.revision,
    canUndo: state ? state.canUndo : false, canRedo: state ? state.canRedo : false };
}
function mapPos(pos, ops) {
  let p={...pos};
  for (const op of ops) {
    if (op.tag!=="blk") continue;
    const i=op.index,c=op.core;
    if(c.tag==="inl" && p.block===i) {
      const x=c.op;
      if(x.tag==="ins" && x.pos<=p.offset) p.offset++;
      else if(x.tag==="del" && x.pos<p.offset) p.offset--;
    } else if(c.tag==="split") {
      if(p.block>i) p.block++;
      else if(p.block===i && p.offset>c.pos){p.block++;p.offset-=c.pos;}
    } else if(c.tag==="merge") {
      if(p.block===i+1){p.block=i;p.offset+=c.pos;}
      else if(p.block>i+1)p.block--;
    }
  }
  return p;
}
function integrate(changes, snapshot) {
  if (!client) return;
  for (let change of changes || []) {
    if (change.revision <= client.revision) continue;
    change = { ...change, edit: (change.edit || []).map(OTClient.decode) };
    const selection=getSelection();
    const selectionInside=!!(selection && selection.rangeCount && editor.contains(selection.anchorNode));
    const caretFocused=selectionInside || document.activeElement===editor;
    let selected=selectionInside ? currentRange() : null;
    if (change.clientId===clientId && requestCounts.has(change.requestId)) {
      const count=requestCounts.get(change.requestId);
      OTClient.acknowledge(client,change,count);
      requestCounts.delete(change.requestId);
    } else {
      const transformedRemote=OTClient.receiveRemote(client,change);
      if(selected) selected={from:mapPos(selected.from,transformedRemote),to:mapPos(selected.to,transformedRemote)};
    }
    snapshotFromClient(); render();
    if(selected)setRange(selected);else if(caretFocused)setCaret(lastPos);
  }
  if (state) {
    if (snapshot) {
      state.canUndo=snapshot.canUndo; state.canRedo=snapshot.canRedo;
      els.undo.disabled=!state.canUndo; els.redo.disabled=!state.canRedo;
    }
    collabStatus.textContent="Connected · revision "+state.rev;
  }
  settleIdle();
}
function settleIdle() {
  if (!activeRequest && (!client || client.pending.length===0)) {
    drainWaiters.splice(0).forEach(r=>r());
    if (!actionPending) idleWaiters.splice(0).forEach(r=>r());
  }
}
async function sendPending() {
  if (!client || activeRequest || !client.pending.length) { settleIdle(); return; }
  const requestId=crypto.randomUUID ? crypto.randomUUID() : clientId+"-"+Date.now()+"-"+Math.random();
  const count=client.pending.length, ops=client.pending.slice();
  activeRequest={requestId,count}; requestCounts.set(requestId,count);
  let failed=false;
  try {
    const response=await fetch("/collab",{method:"POST",headers:{"Content-Type":"application/json"},
      body:JSON.stringify({cmd:"submitOps",room:roomName,clientId,requestId,baseRevision:client.revision,ops:ops.map(OTClient.encode)})}).then(r=>r.json());
    if(!response.ok) throw new Error(response.error||"collaboration request failed");
    integrate(response.changes||[],response);
  } catch(e) { failed=true; showError(String(e)); }
  finally {
    if(activeRequest && activeRequest.requestId===requestId) activeRequest=null;
    if(client && client.pending.length && !failed) sendPending(); else settleIdle();
  }
}
async function poll() {
  if (!client) return;
  try {
    const r=await fetch("/collab?room="+encodeURIComponent(roomName)+"&since="+client.revision,{cache:"no-store"});
    const remote=await r.json();
    if(!remote.ok){collabStatus.textContent="Disconnected";return;}
    integrate(remote.changes||[],remote);
    if(state){
      state.canUndo=remote.canUndo;state.canRedo=remote.canRedo;
      els.undo.disabled=!state.canUndo;els.redo.disabled=!state.canRedo;
    }
    if(client.pending.length&&!activeRequest)sendPending();
  } catch(_) { collabStatus.textContent="Reconnecting…"; }
}
function caretAfterInsert(from,text) {
  const lines=text.replace(/\r\n?/g,"\n").split("\n");
  return lines.length===1 ? {block:from.block,offset:from.offset+cp(lines[0])}
    : {block:from.block+lines.length-1,offset:cp(lines[lines.length-1])};
}
function replace(from,to,text) {
  const ops=OTClient.buildReplace(state.doc,from,to,text);
  if(!ops.length)return;
  OTClient.local(client,ops); snapshotFromClient(); render(); editor.focus();
  setCaret(caretAfterInsert(from,text)); sendPending();
}
function setKind(block,kind) {
  const ops=OTClient.buildKind(state.doc,block,kind); if(!ops.length)return;
  OTClient.local(client,ops); snapshotFromClient(); render(); sendPending();
}
function rangeText(from,to) {
  if(from.block===to.block)return Array.from(state.doc[from.block].text).slice(from.offset,to.offset).join("");
  const parts=[];
  for(let b=from.block;b<=to.block;b++){const a=Array.from(state.doc[b].text);
    parts.push(a.slice(b===from.block?from.offset:0,b===to.block?to.offset:a.length).join(""));}
  return parts.join("\n");
}
function wordBoundary(pos,dir) {
  const a=Array.from(state.doc[pos.block].text);let o=pos.offset;
  if(dir<0){while(o>0&&/\s/.test(a[o-1]))o--;while(o>0&&!/\s/.test(a[o-1]))o--;}
  else{while(o<a.length&&/\s/.test(a[o]))o++;while(o<a.length&&!/\s/.test(a[o]))o++;}
  return {block:pos.block,offset:o};
}
function doUndoRedo(cmd) {
  const run=async()=>{
    actionPending=true;
    try {
      const r=await fetch("/collab",{method:"POST",headers:{"Content-Type":"application/json"},
        body:JSON.stringify({cmd,room:roomName})}).then(x=>x.json());
      if(!r.ok)showError(r.error||cmd+" failed");
      await poll();
    } catch(e){showError(String(e));}
    finally{actionPending=false;settleIdle();}
  };
  if(client.pending.length||activeRequest) {
    actionPending=true;
    new Promise(resolve=>drainWaiters.push(resolve)).then(run);
  } else { actionPending=true; run(); }
}
function whenIdle(){return (activeRequest||actionPending||client?.pending.length)?new Promise(r=>idleWaiters.push(r)):Promise.resolve();}

let compositionRange=null;
editor.addEventListener("compositionstart",()=>{compositionRange=currentRange();});
editor.addEventListener("compositionend",e=>{const r=compositionRange;compositionRange=null;
  if(r)replace(r.from,r.to,e.data||"");});
editor.addEventListener("beforeinput",e=>{
  if(e.isComposing||compositionRange)return;
  e.preventDefault();
  const {from,to}=currentRange(), collapsed=cmp(from,to)===0;
  switch(e.inputType){
    case "insertText": if(e.data)replace(from,to,e.data);break;
    case "insertParagraph":case "insertLineBreak":replace(from,to,"\n");break;
    case "insertFromPaste":case "insertFromDrop":case "insertReplacementText":{
      const t=e.dataTransfer?e.dataTransfer.getData("text/plain"):e.data;if(t)replace(from,to,t);break;}
    case "deleteContentBackward":
      if(!collapsed)replace(from,to,"");
      else if(from.offset>0)replace({block:from.block,offset:from.offset-1},from,"");
      else if(from.block>0)replace({block:from.block-1,offset:blockLen(from.block-1)},from,"");break;
    case "deleteContentForward":
      if(!collapsed)replace(from,to,"");
      else if(from.offset<blockLen(from.block))replace(from,{block:from.block,offset:from.offset+1},"");
      else if(from.block<state.doc.length-1)replace(from,{block:from.block+1,offset:0},"");break;
    case "deleteWordBackward":
      if(!collapsed)replace(from,to,"");else if(from.offset===0&&from.block>0)replace({block:from.block-1,offset:blockLen(from.block-1)},from,"");
      else replace(wordBoundary(from,-1),from,"");break;
    case "deleteWordForward":
      if(!collapsed)replace(from,to,"");else if(from.offset===blockLen(from.block)&&from.block<state.doc.length-1)replace(from,{block:from.block+1,offset:0},"");
      else replace(from,wordBoundary(from,1),"");break;
    case "deleteByCut":if(!collapsed)replace(from,to,"");break;
    case "historyUndo":doUndoRedo("undo");break;case "historyRedo":doUndoRedo("redo");break;
  }
});
editor.addEventListener("cut",e=>{const {from,to}=currentRange();if(cmp(from,to)===0)return;
  if(e.clipboardData)e.clipboardData.setData("text/plain",rangeText(from,to));e.preventDefault();replace(from,to,"");});
editor.addEventListener("keydown",e=>{const mod=e.ctrlKey||e.metaKey,k=(e.key||"").toLowerCase();
  if(mod&&k==="z"){e.preventDefault();doUndoRedo(e.shiftKey?"redo":"undo");}
  else if(mod&&k==="y"){e.preventDefault();doUndoRedo("redo");}});
for(const b of [els.undo,els.redo])b.addEventListener("mousedown",e=>e.preventDefault());
els.undo.addEventListener("click",()=>doUndoRedo("undo"));els.redo.addEventListener("click",()=>doUndoRedo("redo"));
els.kind.addEventListener("change",()=>setKind(lastPos.block,els.kind.value));

fetch("/collab?room="+encodeURIComponent(roomName),{cache:"no-store"}).then(r=>r.json()).then(s=>{
  if(!s.ok)throw new Error(s.error||"cannot load room");
  client=OTClient.createClient(s);state={doc:client.doc,rev:client.revision,canUndo:s.canUndo,canRedo:s.canRedo};
  render();setCaret({block:0,offset:0});collabStatus.textContent="Connected · revision "+state.rev;
}).catch(e=>showError(String(e)));
setInterval(poll,300);
document.getElementById("share-room").addEventListener("click",async()=>{
  const url=new URL(location.href);url.searchParams.set("room",roomName);
  try{await navigator.clipboard.writeText(url.toString());collabStatus.textContent="Invite link copied";}
  catch(_){collabStatus.textContent=url.toString();}
});
window.__editor={whenIdle,get state(){return state;}};
})();