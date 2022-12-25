select distinct TeamId
from Sessions
where
  ContestId = :ContestId and
  SessionId in (
    select Runs.SessionId from Runs
    where Accepted = 1
  )