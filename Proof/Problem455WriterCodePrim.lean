import Problem455WriterCode
import Problem455WriterMachinePrim

namespace P455WriterProgram.Cert

theorem fromCodeBits' : Primrec fromCodeBits := machineData'.comp
  (raw'.comp (Primrec.list_cons.comp (Primrec.const 0) (Primrec.list_cons.comp (Primrec.const 0) readBits')))

end P455WriterProgram.Cert
