select TeamName
from Teams
where
  TeamId in (
    select Sessions.TeamId
    from Sessions
    where
      ContestId = :ContestId and
      SessionId in (
        select Runs.SessionId from Runs
        where Letter = :Letter and Accepted = 1
      )
  )